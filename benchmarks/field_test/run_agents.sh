#!/usr/bin/env bash
# Field test: agents judge arguments with and without hylogic's check_argument tool.
#
# Usage: run_agents.sh [MODEL...]     MODEL: haiku | opus (default: both)
#
# Needs: the `claude` CLI, and a Python with hylogic and mcp importable
# (set PYTHON, default python3). Every run makes real model calls.
set -euo pipefail

if [ "$#" -gt 0 ]; then MODELS=("$@"); else MODELS=(haiku opus); fi
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
PYTHON="${PYTHON:-python3}"
RUN="$HERE/runs/$(date +%Y%m%d-%H%M%S)"
PARALLEL="${PARALLEL:-6}"
ITEMS_FILE="${ITEMS_FILE:-$HERE/items.json}"
mkdir -p "$RUN"

# first-order items (items_fo.json) are formalized with predicates and quantifiers
if grep -q '"first-order"' "$ITEMS_FILE"; then
  TOOL_HINT='You can check your answer with the check_argument tool: formalize each sentence with predicates and quantifiers, such as (forall [x] (=> (Manager x) (Badge x))) and (Badge Anna), and call it.'
else
  TOOL_HINT='You can check your answer with the check_argument tool: formalize each sentence with one letter per simple sentence and call it.'
fi
CONVENTIONS='Use the usual conventions of logic: "or" is inclusive, "unless" means "or", and "A only if B" means "if A, then B".'
ITEMS="${ITEMS:-}"
[ -n "$ITEMS" ] || ITEMS=$("$PYTHON" -c "import json,sys; [print(i['id']) for i in json.load(open('$ITEMS_FILE'))]")

run_one() {
  local condition=$1 model=$2 id=$3
  local dir="$RUN/$condition/$model/$id"
  mkdir -p "$dir"
  local text
  text=$("$PYTHON" -c "import json; print(next(i['text'] for i in json.load(open('$ITEMS_FILE')) if i['id']=='$id'))")
  local prompt="Is the following argument logically valid? An argument is valid when its conclusion must be true whenever all of its premises are true, whatever the facts of the world are. $CONVENTIONS

$text"
  if [ "$condition" = tool ]; then
    prompt="$prompt

$TOOL_HINT"
  fi
  prompt="$prompt

Answer on the last line with exactly VALID or INVALID."
  if [ "$condition" = tool ]; then
    printf '{"mcpServers":{"hylogic":{"type":"stdio","command":"%s","args":["-m","hylogic.mcp_server"],"env":{"PYTHONPATH":"%s","HYLOGIC_MCP_LOG":"%s"}}}}\n' \
      "$PYTHON" "$ROOT" "$dir/tool_calls.jsonl" > "$dir/mcp.json"
    (cd "$dir" && timeout 600 claude -p "$prompt" --model "$model" --tools "" --strict-mcp-config \
      --mcp-config mcp.json --allowedTools mcp__hylogic --no-session-persistence \
      --output-format json > result.json 2> err.txt || true)
  else
    echo '{"mcpServers":{}}' > "$dir/mcp.json"
    (cd "$dir" && timeout 600 claude -p "$prompt" --model "$model" --tools "" --strict-mcp-config \
      --mcp-config mcp.json --no-session-persistence --output-format json > result.json 2> err.txt || true)
  fi
}
export -f run_one
export RUN HERE ROOT PYTHON CONVENTIONS ITEMS_FILE TOOL_HINT

for model in "${MODELS[@]}"; do
  for condition in ${CONDITIONS:-plain tool}; do
    for id in $ITEMS; do echo "$condition $model $id"; done
  done
done | xargs -P "$PARALLEL" -n 3 bash -c 'run_one "$0" "$1" "$2"'

"$PYTHON" "$HERE/score.py" "$RUN" "$ITEMS_FILE"
