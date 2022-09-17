/Applications/Isabelle2021-1.app/bin/isabelle export -x "*:**" -d . arith
mv export/arith.Arith/code/*.ocaml arith_ocaml/lib/
for file in arith_ocaml/lib/*.ocaml; do 
    mv -- "$file" "${file%.ocaml}.ml"
done
# cp export/tapl.Tapl/code/*.ocaml tapl_ocaml/lib/
