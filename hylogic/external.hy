"A bridge to E and Vampire: their search, HyLogic's presentation.

HyLogic's own prover is meant to be read; E and Vampire are built to be fast.
This module hands a problem to either of them, reads the proof they print in
TSTP (the TPTP proof format), and presents it the HyLogic way: numbered steps,
formulas in logical notation, and for each step its rule and parent steps.

  (prove-external '(Mortal socrates) ['(∀ [x] (→ (Man x) (Mortal x))) '(Man socrates)])

The provers are found on PATH as vampire and eprover, or through the
environment variables HYLOGIC_VAMPIRE and HYLOGIC_EPROVER."

(import os
        re
        shutil
        subprocess
        tempfile
        pathlib [Path]
        hylogic.tptp [Parser tokens TPTPError]
        hylogic.formulas [pretty]
        hylogic.export [to-tptp])

(defn prover-path [prover]
  "The executable for vampire or eprover, or None if it is not installed."
  (setv env (os.environ.get (+ "HYLOGIC_" (.upper prover))))
  (if (and env (os.path.exists env)) env (shutil.which prover)))

(defn _command [prover path time-limit]
  (setv exe (prover-path prover))
  (when (is exe None)
    (raise (FileNotFoundError f"{prover} is not installed; set HYLOGIC_{(.upper prover)} or put it on PATH")))
  (if (= prover "vampire")
      [exe "--mode" "casc" "-t" f"{(int time-limit)}s" "--proof" "tptp" (str path)]
      [exe "--auto" "--silent" "--tstp-format" "--proof-object" f"--cpu-limit={(int time-limit)}" (str path)]))

;; Reading TSTP

(defn _general [p]
  "A TSTP general term: word, word(args), [list], string or number, as nested lists."
  (setv [kind value] (.take p))
  (cond
    (= value "[")
      (do
        (setv items [])
        (while (not (.at p "]"))
          (.append items (_general p))
          (when (.at p ",") (.take p ",")))
        (.take p "]")
        items)
    (.at p "(")
      (do
        (.take p "(")
        (setv args [])
        (while (not (.at p ")"))
          (.append args (_general p))
          (when (.at p ",") (.take p ",")))
        (.take p ")")
        #(value #* args))
    (and (.at p ":") (!= kind "op")) (do (.take p ":") #(":" value (_general p)))
    True value))

(defn _source [term]
  "#(rule parents) from a TSTP source term; nested inferences are unwrapped."
  (cond
    (and (isinstance term tuple) (= (get term 0) "inference"))
      (do
        (setv rule (get term 1) parents [] inner [])
        (for [x (get term 3)]
          (if (and (isinstance x tuple) (= (get x 0) "inference"))
              (do (setv [r ps] (_source x)) (.append inner r) (+= parents ps))
              (when (isinstance x str) (.append parents x))))
        #((.join " ∘ " [rule #* inner]) parents))
    (and (isinstance term tuple) (= (get term 0) "file")) #("input" [])
    (and (isinstance term tuple) (= (get term 0) "introduced")) #(f"introduced {(get term 1)}" [])
    True #("" [])))

(defclass Step []
  (defn __init__ [self name role formula rule parents]
    (setv self.name name self.role role self.formula formula self.rule rule self.parents parents)))

(defn read-tstp [text]
  "The steps of the TSTP proof in a prover's output."
  (setv m (re.search r"SZS output start[^\n]*\n(.*?)\n[^\n]*SZS output end" text re.S))
  (when (not m) (return []))
  (setv body (re.sub r"(?m)^#.*$" "" (.group m 1))
        p (Parser (tokens body))
        steps [])
  (while (is-not (get (.peek p) 0) None)
    (setv [_ kind] (.take p))
    (.take p "(")
    (setv name (get (.take p) 1))
    (.take p ",")
    (setv role (get (.take p) 1))
    (.take p ",")
    (setv formula (.logic p) rule "" parents [])
    (when (.at p ",")
      (.take p ",")
      (setv [rule parents] (_source (_general p)))
      (while (.at p ",") (.take p ",") (_general p)))
    (.take p ")") (.take p ".")
    (.append steps (Step name role formula rule parents)))
  steps)

(defclass ExternalResult []
  "What E or Vampire found: the SZS status and the proof steps, if any."
  (defn __init__ [self prover status steps output]
    (setv self.prover prover self.status status self.steps steps self.output output))
  (defn [property] proved [self] (in self.status #{"Theorem" "Unsatisfiable"}))
  (defn proof [self]
    "The proof as numbered lines, like HyLogic's own proofs."
    (setv numbers (dfor [i s] (enumerate self.steps) s.name (+ i 1)))
    (lfor [i s] (enumerate self.steps)
      (+ (.rjust (str (+ i 1)) 4) ". " (.ljust (pretty s.formula) 44) " "
         (if s.parents
             (+ s.rule " " (.join ", " (gfor q s.parents (str (.get numbers q q)))))
             (if (in s.role #{"conjecture" "negated_conjecture"}) s.role (or s.rule s.role)))))))

(defn run-prover [path [prover "vampire"] [time-limit 10]]
  "Run E or Vampire on a TPTP file and read its answer."
  (try
    (setv out (. (subprocess.run (_command prover path time-limit) :capture-output True :text True
                                 :timeout (+ time-limit 10))
                 stdout))
    (except [subprocess.TimeoutExpired] (return (ExternalResult prover "Timeout" [] ""))))
  (setv m (re.search r"SZS status (\w+)" out)
        status (if m (.group m 1) "Unknown")
        steps [])
  (try
    (setv steps (read-tstp out))
    (except [e TPTPError] (setv steps [])))
  (ExternalResult prover status steps out))

(defn prove-external [goal [axioms #()] [prover "vampire"] [time-limit 10]]
  "Prove goal from axioms with E or Vampire, through a temporary TPTP file."
  (with [d (tempfile.TemporaryDirectory)]
    (setv path (/ (Path d) "problem.p"))
    (.write-text path (to-tptp axioms goal))
    (run-prover path prover time-limit)))
