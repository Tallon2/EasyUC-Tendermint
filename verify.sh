#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
easycrypt=${EASYCRYPT:-easycrypt}
dsl_dir=${EASYUC_DSL_DIR:-../EasyUC/uc-dsl}
ucdsl=${UCDSL:-$dsl_dir/bin/ucdsl}
if [[ ! -x "$ucdsl" && -z ${UCDSL:-} ]]; then
  ucdsl=ucdsl
fi
if ! command -v "$easycrypt" >/dev/null || ! command -v "$ucdsl" >/dev/null; then
  echo 'Install EasyCrypt and build ucdsl, or set EASYCRYPT and UCDSL to their executable paths.' >&2
  exit 1
fi
if [[ ! -d "$dsl_dir/prelude" || ! -d "$dsl_dir/common" ]]; then
  echo 'Set EASYUC_DSL_DIR to the EasyUC uc-dsl directory.' >&2
  exit 1
fi

"$easycrypt" config | sed -n '1p'
"$ucdsl" -version
"$easycrypt" llm -lastgoals WeightedQuorum.ec
printf '%s\n' 'PASS EasyCrypt: weighted inclusion-exclusion, strict intersection bound, honest overlap, certificate uniqueness'
"$easycrypt" llm -lastgoals SingleRound.ec
printf '%s\n' 'PASS EasyCrypt: single honest precommit, authenticated delivery, certified decisions, same-round agreement, replay idempotence'

"$ucdsl" -I "$dsl_dir/prelude" -I "$dsl_dir/common" -units TendermintRound.uc
printf '%s\n' 'PASS EasyUC: type and unit checking'
"$ucdsl" -I "$dsl_dir/prelude" -I "$dsl_dir/common" -batch demo.uci
assertions=$(awk '/^assert / { n++ } END { print n+0 }' demo.uci)
printf 'PASS EasyUC: all %s interpreter assertions\n' "$assertions"
printf '%s\n' \
  '  Voters: weights (3,2,2,2); Byzantine voter 3; quorum weight > 6.' \
  '  Honest node 1: weight 3 before and after a replay; weight 5 is insufficient; weight 7 enables Decide(1,42).' \
  '  Honest nodes 0 and 2 also emit Decide for block 42 (certificate weights 9 and 7).' \
  '  Byzantine equivocation is accepted under its own identity; unpublished delivery and repeat honest precommit are rejected.'
