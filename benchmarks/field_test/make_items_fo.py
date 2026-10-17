"""Generate first-order arguments for the field test, with validity decided twice.

The first field test used short arguments, mostly propositional, and the
models judged them well without a checker. These are longer: chains of three
to six steps with quantifiers and relations, about people in an office.

A valid item needs every premise: HyLogic's proof uses all of them (see
Argument.used). An invalid item is made from a valid chain by one change a
hasty reader can miss, and records which:

  converse    one rule turned around: "everyone who has a badge is a manager"
              where the chain needs "every manager has a badge"
  some        one "everyone who" weakened to "at least one person who"
  scope       "everyone trusts someone" read as "someone is trusted by everyone"
  other       the chain starts from a fact about another person

Validity is decided by HyLogic and checked with Z3; an item where they
disagree, or either cannot decide, is dropped. Half the items are valid.

With --hard the chains are 10 to 16 premises long and run through two
people (facts about b, "a reports to b", "everyone who reports to someone
who ... "), with two to four distractors that sound relevant, such as the
converse of a chain rule, and the premises in random order. A valid hard item
rests on exactly its chain: the proof uses no distractor.

With --harder a valid chain also needs a contrapositive step ("no one on
call is in the union; everyone with an archive key is in the union; Eva is on
call", so Eva has no key), a case split ("everyone who ... is remote or on
nights, or both", both branches leading on) and a transitive relation through
three people, among four to six distractors. Its traps add `branch` (one case
leads elsewhere) and `direction` (a relation fact turned around).

With --hardest the chain needs two contrapositive steps and two case splits,
one of each before and after the relation step, about 25 to 30 premises.

    TPTP-free; needs z3:  python make_items_fo.py [N] [--hard | --harder | --hardest] > items_fo.json
"""
import json
import random
import sys

import hy  # noqa: F401
import z3

from hylogic.argument import Argument
from hylogic.export import to_smtlib
from hylogic.formulas import pretty

PEOPLE = ["Anna", "Ben", "Carla", "David", "Eva", "Farid"]

# a property: name, "x <phrase>" in the singular, and its negation
PROPERTIES = [
    ("Manager", "is a manager", "is not a manager"),
    ("Engineer", "is an engineer", "is not an engineer"),
    ("Badge", "has a badge", "does not have a badge"),
    ("Lab", "can enter the lab", "cannot enter the lab"),
    ("Remote", "works remotely", "does not work remotely"),
    ("Laptop", "has a company laptop", "does not have a company laptop"),
    ("Training", "has done the safety training", "has not done the safety training"),
    ("Payroll", "can see the payroll", "cannot see the payroll"),
    ("Oncall", "is on call this week", "is not on call this week"),
    ("Mentor", "mentors a trainee", "does not mentor a trainee"),
    ("Parking", "has a parking space", "does not have a parking space"),
    ("Night", "works the night shift", "does not work the night shift"),
    ("Union", "is in the union", "is not in the union"),
    ("Archive", "has a key to the archive", "does not have a key to the archive"),
    ("Lead", "is a team lead", "is not a team lead"),
    ("Vpn", "uses the VPN", "does not use the VPN"),
    ("Monday", "attends the Monday meeting", "does not attend the Monday meeting"),
    ("Finnish", "speaks Finnish", "does not speak Finnish"),
]
# a relation: name, "x <phrase> y"
RELATIONS = [("ReportsTo", "reports to"), ("Trusts", "trusts"), ("Mentors", "mentors")]


def lower(s):
    """A sentence continued after "Therefore,": lowercase unless it starts with a name."""
    return s if s.split()[0] in PEOPLE else s[0].lower() + s[1:]


def X(p):
    return (p, "x")


def every(p, q):  # everyone who p, q
    return ("forall", ("x",), ("=>", X(p[0]), X(q[0]))), f"Everyone who {p[1]} {q[1]}."


def no_one(p, q):  # no one who p, q
    return ("forall", ("x",), ("=>", X(p[0]), ("not", X(q[0])))), f"No one who {p[1]} {q[1]}."


def only(p, q):  # only someone who p, q   (q -> p)
    return ("forall", ("x",), ("=>", X(q[0]), X(p[0]))), f"Only someone who {p[1]} {q[1]}."


def some(p, q):
    # not "someone who p, q": English also reads that as a rule ("someone who
    # knows the code can open the door"), and the field test pilot did so
    return ("exists", ("x",), ("and", X(p[0]), X(q[0]))), f"At least one person who {p[1]} {q[1]}."


def fact(name, p, positive=True):
    atom = (p[0], name)
    return (atom if positive else ("not", atom)), f"{name} {p[1] if positive else p[2]}."


def rel_fact(r, a, b):
    return (r[0], a, b), f"{a} {r[1]} {b}."


def via(r, p, q):  # everyone who <r> someone who p, q
    return (("forall", ("x", "y"), ("=>", ("and", (r[0], "x", "y"), (p[0], "y")), (q[0], "x"))),
            f"Everyone who {r[1]} someone who {p[1]} {q[1]}.")


def chain(rng):
    """A valid argument: premises [(formula, text)], conclusion (formula, text), and the
    places where a hasty change would break it."""
    props = rng.sample(PROPERTIES, 6)
    a, b = rng.sample(PEOPLE, 2)
    r = rng.choice(RELATIONS)
    premises, spots = [], []
    shape = rng.choice(["plain", "relation", "negative", "only", "exists"])
    k = rng.randint(2, 4)  # rules in the chain
    if shape == "relation":
        # b has p0; a <r> b; everyone who <r> someone who p0 has p1; chain from p1
        premises += [fact(b, props[0]), rel_fact(r, a, b), via(r, props[0], props[1])]
        spots.append(("other", 0))
        start, subject = 1, a
    else:
        premises.append(fact(a, props[0]))
        spots.append(("other", 0))
        start, subject = 0, a
    for i in range(start, start + k):
        # "only someone who <p_i+1> <p_i>" says p_i -> p_i+1, the same step in words
        # people often read the other way round
        rule = only(props[i + 1], props[i]) if shape == "only" and i == start else every(props[i], props[i + 1])
        premises.append(rule)
        spots.append(("converse", len(premises) - 1))
        spots.append(("some", len(premises) - 1))
    last = props[start + k]
    if shape == "negative":
        extra = props[start + k + 1] if start + k + 1 < len(props) else props[-1]
        premises.append(no_one(last, extra))
        spots.append(("converse", len(premises) - 1))
        conclusion = fact(subject, extra, positive=False)
    elif shape == "exists":
        conclusion = (("exists", ("x",), X(last[0])), f"Someone {last[1]}.")
    else:
        conclusion = fact(subject, last)
    return premises, conclusion, spots, (a, b, r, props)


def perturb(rng, premises, conclusion, spots, ctx):
    a, b, r, props = ctx
    # "another person" is the easiest change to spot, so it is drawn less often
    kind, at = rng.choice([s for s in spots if s[0] != "other"] * 3 + [s for s in spots if s[0] == "other"])
    ps = list(premises)
    f, text = ps[at]
    if kind == "other":
        c = rng.choice([p for p in PEOPLE if p not in (a, b)])
        if f[0] in [p[0] for p in PROPERTIES]:
            prop = next(p for p in PROPERTIES if p[0] == f[0])
            ps[at] = fact(c, prop)
    elif kind == "converse" and f[0] == "forall":
        body = f[2]
        if body[0] == "=>" and body[2][0] != "not":
            p = next(x for x in PROPERTIES if x[0] == body[1][0])
            q = next(x for x in PROPERTIES if x[0] == body[2][0])
            ps[at] = every(q, p)
        elif body[0] == "=>":
            p = next(x for x in PROPERTIES if x[0] == body[1][0])
            q = next(x for x in PROPERTIES if x[0] == body[2][1][0])
            ps[at] = only(q, p) if rng.random() < 0.5 else ps[at]
    elif kind == "some" and f[0] == "forall" and f[2][0] == "=>" and f[2][2][0] != "not":
        p = next(x for x in PROPERTIES if x[0] == f[2][1][0])
        q = next(x for x in PROPERTIES if x[0] == f[2][2][0])
        ps[at] = some(p, q)
    return ps, kind


def scope_item(rng):
    """Everyone <r> someone who p; ... ⊬ someone who p is <r>-ed by everyone (and a valid twin)."""
    r = rng.choice(RELATIONS)
    p, q = rng.sample(PROPERTIES, 2)
    a = rng.choice(PEOPLE)
    every_some = (("forall", ("x",), ("exists", ("y",), ("and", (p[0], "y"), (r[0], "x", "y")))),
                  f"Everyone {r[1]} someone who {p[1]}.")
    rule = every(p, q)
    invalid = rng.random() < 0.5
    if invalid:
        concl = (("exists", ("y",), ("and", (q[0], "y"), ("forall", ("x",), (r[0], "x", "y")))),
                 f"Someone who {q[1]} is someone everyone {r[1]}.")
        return [every_some, rule], concl, "scope"
    concl = (("exists", ("y",), ("and", (q[0], "y"), (r[0], a, "y"))),
             f"{a} {r[1]} someone who {q[1]}.")
    return [every_some, rule], concl, None


def hard_chain(rng):
    """A long valid chain through two people, with distractors, premises shuffled.
    Returns premises, conclusion, the indices of the chain premises, the places
    a trap may go, and the context."""
    props = rng.sample(PROPERTIES, 16)
    a, b = rng.sample(PEOPLE, 2)
    r = rng.choice(RELATIONS)
    m = rng.randint(3, 5)            # rules about b
    n = rng.randint(4, 6)            # rules about a, after the relation step
    chain = [fact(b, props[0])]
    for i in range(m):
        rule = only(props[i + 1], props[i]) if i == 1 else every(props[i], props[i + 1])
        chain.append(rule)
    chain += [rel_fact(r, a, b), via(r, props[m], props[m + 1])]
    for i in range(m + 1, m + 1 + n):
        chain.append(every(props[i], props[i + 1]))
    last = props[m + 1 + n]
    if rng.random() < 0.4:
        extra = props[m + 2 + n]
        chain.append(no_one(last, extra))
        conclusion = fact(a, extra, positive=False)
        used_props = m + 3 + n
    else:
        conclusion = fact(a, last)
        used_props = m + 2 + n
    # distractors: a converse of a chain rule, a fact about someone else, rules
    # among properties the chain does not use
    spare = props[used_props:]
    distractors = []
    i = rng.randint(1, m - 1)
    distractors.append(every(props[i + 1], props[i]))
    c = rng.choice([p for p in PEOPLE if p not in (a, b)])
    distractors.append(fact(c, rng.choice(props[1:used_props])))
    for _ in range(rng.randint(0, 2)):
        if len(spare) >= 2:
            p, q = rng.sample(spare, 2)
            distractors.append(rng.choice([every, no_one])(p, q))
    premises = chain + distractors
    order = list(range(len(premises)))
    rng.shuffle(order)
    shuffled = [premises[k] for k in order]
    chain_at = sorted(order.index(k) for k in range(len(chain)))
    spots = [("other", order.index(0))]
    for k in range(1, len(chain)):
        f = chain[k][0]
        if f[0] == "forall" and f[2][0] == "=>" and f[2][1][0] != "and":
            spots += [("converse", order.index(k)), ("some", order.index(k))]
    return shuffled, conclusion, chain_at, spots, (a, b, r, props)


def unless_not(p, q):  # everyone who does not p, q
    return ("forall", ("x",), ("=>", ("not", X(p[0])), X(q[0]))), f"Everyone who {p[2]} {q[1]}."


def either(p, q1, q2):  # everyone who p, q1 or q2 (or both)
    return (("forall", ("x",), ("=>", X(p[0]), ("or", X(q1[0]), X(q2[0])))),
            f"Everyone who {p[1]} {q1[1]} or {q2[1]}, or both.")


def transitive(r):
    return (("forall", ("x", "y", "z"), ("=>", ("and", (r[0], "x", "y"), (r[0], "y", "z")), (r[0], "x", "z"))),
            f"Anyone who {r[1]} someone who {r[1]} a third person also {r[1]} that third person.")


def harder_chain(rng):
    """A valid chain that needs a contrapositive step, a case split and a
    transitive relation through three people, among distractors, shuffled.
    Returns premises, conclusion, chain indices, trap spots and the trap makers."""
    props = rng.sample(PROPERTIES, 18)
    a, b, c = rng.sample(PEOPLE, 3)
    r = (("ReportsTo", "reports to"))
    it = iter(props)
    nxt = lambda: next(it)
    chain, traps = [], []
    # about c: forward steps, then modus tollens to a negative property
    p = nxt()
    chain.append(fact(c, p))
    for _ in range(rng.randint(1, 2)):
        q = nxt()
        chain.append(every(p, q))
        traps.append(("converse", len(chain) - 1, (p, q)))
        p = q
    blocked, neg = nxt(), nxt()
    chain.append(no_one(p, blocked))                   # c is not <blocked>
    chain.append(every(neg, blocked))                  # so c is not <neg> (tollens)
    traps.append(("converse", len(chain) - 1, (neg, blocked)))
    p = nxt()
    chain.append(unless_not(neg, p))                   # c does not <neg>, so <p>
    # a case split
    q1, q2, joined = nxt(), nxt(), nxt()
    chain.append(either(p, q1, q2))
    chain.append(every(q1, joined))
    chain.append(every(q2, joined))
    traps.append(("branch", len(chain) - 1, (q2, joined)))
    p = joined
    # a reports to b, b reports to c: a reports to c, and the rule needs that
    chain.append(rel_fact(r, a, b))
    traps.append(("direction", len(chain) - 1, (b, a)))
    chain.append(rel_fact(r, b, c))
    chain.append(transitive(r))
    q = nxt()
    chain.append(via(r, p, q))
    p = q
    for _ in range(rng.randint(2, 3)):
        q = nxt()
        chain.append(every(p, q))
        traps.append(("converse", len(chain) - 1, (p, q)))
        traps.append(("some", len(chain) - 1, (p, q)))
        p = q
    conclusion = fact(a, p)
    spare = list(it)
    distractors = [every(chain_q, chain_p) for chain_p, chain_q in
                   [rng.choice([t[2] for t in traps if t[0] == "converse"])]]
    d = rng.choice([x for x in PEOPLE if x not in (a, b, c)])
    distractors.append(fact(d, rng.choice(props[:10])))
    distractors.append(rel_fact(r, d, a))
    for _ in range(rng.randint(2, 3)):
        if len(spare) >= 2:
            x, y = rng.sample(spare, 2)
            distractors.append(rng.choice([every, no_one, unless_not])(x, y))
    return chain, distractors, conclusion, traps, r


class _Chain:
    """A chain under construction: premises, traps, the property reached so far,
    and fresh properties to draw from."""
    def __init__(self, rng, props):
        self.rng, self.props, self.premises, self.traps = rng, iter(props), [], []

    def fresh(self):
        return next(self.props)

    def add(self, premise, trap=None):
        self.premises.append(premise)
        if trap:
            self.traps.append((trap[0], len(self.premises) - 1, trap[1]))

    def forward(self, p, n):
        for _ in range(n):
            q = self.fresh()
            self.add(every(p, q), ("converse", (p, q)))
            self.traps.append(("some", len(self.premises) - 1, (p, q)))
            p = q
        return p

    def tollens(self, p):
        """From p: no one who p is <blocked>; everyone who <neg> is <blocked>;
        so not <neg>; everyone who does not <neg> has <q>. Returns q."""
        blocked, neg, q = self.fresh(), self.fresh(), self.fresh()
        self.add(no_one(p, blocked))
        self.add(every(neg, blocked), ("converse", (neg, blocked)))
        self.add(unless_not(neg, q))
        return q

    def split(self, p):
        """Everyone who p is q1 or q2; both lead to <joined>. Returns joined."""
        q1, q2, joined = self.fresh(), self.fresh(), self.fresh()
        self.add(either(p, q1, q2))
        self.add(every(q1, joined), ("branch", (q1, joined)))
        self.add(every(q2, joined), ("branch", (q2, joined)))
        return joined


def hardest_chain(rng):
    """Two contrapositive steps and two case splits, one of each about c and
    about a, joined by a transitive relation through b, among distractors."""
    a, b, c = rng.sample(PEOPLE, 3)
    r = ("ReportsTo", "reports to")
    props = rng.sample(PROPERTIES, len(PROPERTIES))
    ch = _Chain(rng, props)
    p = ch.fresh()
    ch.add(fact(c, p), ("other", (c, p)))
    p = ch.forward(p, 1)
    p = ch.tollens(p)
    p = ch.split(p)
    ch.add(rel_fact(r, a, b), ("direction", (b, a)))
    ch.add(rel_fact(r, b, c))
    ch.add(transitive(r))
    q = ch.fresh()
    ch.add(via(r, p, q))
    p = ch.tollens(q)
    p = ch.split(p)
    p = ch.forward(p, 1)
    conclusion = fact(a, p)
    spare = list(ch.props)
    distractors = []
    x, y = rng.choice([t[2] for t in ch.traps if t[0] == "converse"])
    distractors.append(every(y, x))
    d = rng.choice([z for z in PEOPLE if z not in (a, b, c)])
    distractors.append(fact(d, rng.choice(props[:8])))
    distractors.append(rel_fact(r, d, a))
    for _ in range(3):
        if len(spare) >= 2:
            u, v = rng.sample(spare, 2)
            distractors.append(rng.choice([every, no_one, unless_not])(u, v))
    return ch.premises, distractors, conclusion, ch.traps, r


def harder_main(want, make=None, prefix="X", seed=2028):
    rng = random.Random(seed)
    items, counts, seen = [], {True: 0, False: 0}, set()
    while len(items) < want:
        chain, distractors, concl, traps, r = (make or harder_chain)(rng)
        kind = None
        if rng.random() < 0.5:
            kind, at, (x, y) = rng.choice(traps)
            if kind == "converse":
                chain[at] = every(y, x)
            elif kind == "some":
                chain[at] = some(x, y)
            elif kind == "branch":
                # one branch leads elsewhere: the case split no longer closes
                other = next(p for p in PROPERTIES if p not in (x, y))
                chain[at] = every(x, other)
            elif kind == "direction":
                chain[at] = rel_fact(r, x, y)
            elif kind == "other":
                d = next(z for z in PEOPLE if z not in (x,) and z not in str(chain))
                chain[at] = fact(d, y)
        premises = chain + distractors
        order = list(range(len(premises)))
        rng.shuffle(order)
        ps = [premises[k] for k in order]
        chain_at = sorted(order.index(k) for k in range(len(chain)))
        pfs, cf = [p[0] for p in ps], concl[0]
        key = (tuple(map(str, pfs)), str(cf))
        # a distractor may not repeat a premise word for word
        if key in seen or len(set(key[0])) < len(pfs):
            continue
        arg = Argument(pfs, cf, timeout=10)
        valid = arg.valid
        if valid is None or z3_valid(pfs, cf) is not valid:
            continue
        if valid == (kind is not None) or counts[valid] >= want // 2:
            continue
        if valid and arg.used != [k + 1 for k in chain_at]:
            continue
        if Argument(pfs, "false", timeout=10).valid is True:
            continue
        seen.add(key)
        counts[valid] += 1
        items.append({"id": f"{prefix}{len(items) + 1}", "kind": "first-order", "trap": kind,
                      "text": " ".join(p[1] for p in ps) + " Therefore, " + lower(concl[1]),
                      "premises": [pretty(f) for f in pfs], "conclusion": pretty(cf),
                      "premise_terms": pfs, "conclusion_term": cf, "valid": valid,
                      "steps": len(pfs), "needed": [k + 1 for k in chain_at]})
    return items


def hard_main(want):
    rng = random.Random(2027)
    items, counts, seen = [], {True: 0, False: 0}, set()
    while len(items) < want:
        ps, concl, chain_at, spots, ctx = hard_chain(rng)
        kind = None
        if rng.random() < 0.5:
            ps, kind = perturb(rng, ps, concl, spots, ctx)
        pfs, cf = [p[0] for p in ps], concl[0]
        key = (tuple(map(str, pfs)), str(cf))
        # a distractor may not repeat a premise word for word
        if key in seen or len(set(key[0])) < len(pfs):
            continue
        arg = Argument(pfs, cf, timeout=10)
        valid = arg.valid
        if valid is None or z3_valid(pfs, cf) is not valid:
            continue
        if valid == (kind is not None) or counts[valid] >= want // 2:
            continue
        # a valid item rests on exactly its chain: the proof uses no distractor
        if valid and arg.used != [k + 1 for k in chain_at]:
            continue
        if Argument(pfs, "false", timeout=10).valid is True:
            continue
        seen.add(key)
        counts[valid] += 1
        items.append({"id": f"H{len(items) + 1}", "kind": "first-order", "trap": kind,
                      "text": " ".join(p[1] for p in ps) + " Therefore, " + lower(concl[1]),
                      "premises": [pretty(f) for f in pfs], "conclusion": pretty(cf),
                      "premise_terms": pfs, "conclusion_term": cf, "valid": valid,
                      "steps": len(pfs), "needed": [k + 1 for k in chain_at]})
    return items


def z3_valid(premises, conclusion):
    s = z3.Solver()
    s.set("timeout", 10000)
    s.from_string(to_smtlib(premises, conclusion, check_sat=False))
    out = s.check()
    if out == z3.unsat:
        return True
    if out == z3.sat:
        return False
    return None


def main():
    args = [x for x in sys.argv[1:] if x != "--hard"]
    want = int(args[0]) if args else 40
    args = [x for x in args if x not in ("--harder", "--hardest")]
    want = int(args[0]) if args else 40
    if "--hardest" in sys.argv:
        json.dump(harder_main(want, hardest_chain, "Z", 2029), sys.stdout, ensure_ascii=False, indent=1)
        print()
        return
    if "--harder" in sys.argv:
        json.dump(harder_main(want), sys.stdout, ensure_ascii=False, indent=1)
        print()
        return
    if "--hard" in sys.argv:
        json.dump(hard_main(want), sys.stdout, ensure_ascii=False, indent=1)
        print()
        return
    rng = random.Random(2026)
    items, counts, seen = [], {True: 0, False: 0}, set()
    while len(items) < want:
        if rng.random() < 0.1:
            ps, concl, kind = scope_item(rng)
        else:
            ps, concl, spots, ctx = chain(rng)
            kind = None
            if rng.random() < 0.5:
                ps, kind = perturb(rng, ps, concl, spots, ctx)
        pfs, cf = [p[0] for p in ps], concl[0]
        key = (tuple(map(str, pfs)), str(cf))
        if key in seen:
            continue
        arg = Argument(pfs, cf, timeout=5)
        valid = arg.valid
        if valid is None or z3_valid(pfs, cf) is not valid:
            continue
        if kind != "scope" and len(pfs) < 3:
            continue  # chains are at least three premises long
        if valid and kind is not None:
            continue  # the change happened not to break the chain
        if not valid and kind is None:
            continue
        if counts[valid] >= want // 2:
            continue
        # a valid item needs every premise; no item is decided by contradictory premises
        if valid and arg.used != list(range(1, len(pfs) + 1)):
            continue
        if Argument(pfs, "false", timeout=5).valid is True:
            continue
        seen.add(key)
        counts[valid] += 1
        items.append({"id": f"F{len(items) + 1}", "kind": "first-order", "trap": kind,
                      "text": " ".join(p[1] for p in ps) + " Therefore, " + lower(concl[1]),
                      "premises": [pretty(f) for f in pfs], "conclusion": pretty(cf),
                      "premise_terms": pfs, "conclusion_term": cf, "valid": valid,
                      "steps": len(pfs)})
    json.dump(items, sys.stdout, ensure_ascii=False, indent=1)
    print()


if __name__ == "__main__":
    main()
