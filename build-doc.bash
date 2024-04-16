#!/usr/bin/env bash
set -eu

BAK_SUFFIX=.bak

# 終わったら.bakファイルに戻す
catch() {
  local CODE=$?
  echo "Restoring from backup..." 2>&1
  find HelloTypeSystem -type f -name "*.lean" \
    | xargs -r -I{} mv -f {}.bak {}
  exit ${CODE}
}

trap catch EXIT

# HelloTypeSystem.leanの最初のコメント`/-! ... -/`をプリアンブルとする。
PREAMBLE=`awk '/^\/-!/,/^-\//{print} /^-\//{exit}' HelloTypeSystem.lean | sed 's!\\\\!\\\\\\\\!g' | tr "\r\n" '  '`

find HelloTypeSystem -type f | xargs -r sed -i"${BAK_SUFFIX}" -ze "s@\(namespace.*\)\$@${PREAMBLE}\n\\1@"

lake -R -Kenv=dev update

# rebuild only did not update docs...
rm -rf .lake/build/doc/HelloTypeSystem*
lake -R -Kenv=dev build HelloTypeSystem:docs
