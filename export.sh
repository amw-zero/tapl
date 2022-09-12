/Applications/Isabelle2021-1.app/bin/isabelle export -x "*:**" -d . tapl
mv export/tapl.Tapl/code/*.ocaml tapl_ocaml/lib/
for file in tapl_ocaml/lib/*.ocaml; do 
    mv -- "$file" "${file%.ocaml}.ml"
done
# cp export/tapl.Tapl/code/*.ocaml tapl_ocaml/lib/
