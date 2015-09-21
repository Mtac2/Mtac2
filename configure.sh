#!/usr/bin/env sh

# Makefile generation
coq_makefile -f Make -o Makefile

# git pre-commit hooks installation
(cd .git/hooks; ln -sf ../../scripts/hooks/pre-commit)

# .merlin generation
# NOTE: Needed because Coq doesn't install any META files
path=`ocamlfind printconf destdir`
if [ $? -ne 0 ]; then
    echo "Warning: Optional command (ocamlfind) not found. Error ignored"
    exit 0
fi

content="
S src\n\
B src\n\
\n\
FLG -rectypes\n\
\n\
PKG camlp4.lib\n\
\n\
# Locates Coq's library\n\
B $path/coq/config\n\
B $path/coq/engine\n\
B $path/coq/grammar\n\
B $path/coq/interp\n\
B $path/coq/intf\n\
B $path/coq/kernel\n\
B $path/coq/lib\n\
B $path/coq/library\n\
B $path/coq/parsing\n\
B $path/coq/plugins\n\
B $path/coq/plugins/btauto\n\
B $path/coq/plugins/cc\n\
B $path/coq/plugins/decl_mode\n\
B $path/coq/plugins/derive\n\
B $path/coq/plugins/extraction\n\
B $path/coq/plugins/firstorder\n\
B $path/coq/plugins/fourier\n\
B $path/coq/plugins/funind\n\
B $path/coq/plugins/micromega\n\
B $path/coq/plugins/nsatz\n\
B $path/coq/plugins/omega\n\
B $path/coq/plugins/quote\n\
B $path/coq/plugins/romega\n\
B $path/coq/plugins/rtauto\n\
B $path/coq/plugins/setoid_ring\n\
B $path/coq/plugins/syntax\n\
B $path/coq/plugins/xml\n\
B $path/coq/pretyping\n\
B $path/coq/printing\n\
B $path/coq/proofs\n\
B $path/coq/stm\n\
B $path/coq/tactics\n\
B $path/coq/toplevel\n\
"

echo -n $content > .merlin
