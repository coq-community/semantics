all : example.vo example2.vo little proof_sqrt.vo test_vcg.lil ex_i.vo

.SUFFIXES: .v .vo

.v.vo:
	$(COQBIN)coqc $*

abstract_i.vo : abstract_i.v intervals.vo axiom.vo
intervals.vo : intervals.v
axiom.vo: axiom.v denot.vo
denot.vo: denot.v function_cpo.vo constructs.vo little.vo
constructs.vo: constructs.v function_cpo.vo
function_cpo.vo: function_cpo.v
little.vo: little.v syntax.vo
syntax.vo: syntax.v
little_w_string.vo : little_w_string.v abstract_i.vo
parser.vo: parser.v little_w_string.vo
example.vo: example.v parser.vo
example2.vo: example2.v little.vo parser.vo axiom.vo
ex_i.vo : ex_i.v parser.vo little.vo axiom.vo abstract_i.vo
extract_interpret.vo : extract_interpret.v abstract_i.vo
proof_sqrt.vo : proof_sqrt.v

little : str_little.cmo interp.cmi interp.cmo parse_little.cmo llex.cmo \
           little.ml
	ocamlc -o little interp.cmo nums.cma str_little.cmo parse_little.cmo \
          llex.cmo little.ml

interp.mli interp.ml : extract_interpret.vo

interp.cmo : interp.ml interp.cmi
	ocamlc -c interp.ml

interp.cmi : interp.mli
	ocamlc interp.mli

parse_little.mli parse_little.ml : parse_little.mly
	ocamlyacc parse_little.mly

str_little.cmo : str_little.ml interp.cmi
	ocamlc -c str_little.ml

llex.ml : llex.mll
	ocamllex llex.mll

llex.cmo : llex.ml parse_little.cmi
	ocamlc -c llex.ml

parse_little.cmi : parse_little.mli str_little.cmi interp.cmi
	ocamlc parse_little.mli

parse_little.cmo : parse_little.cmi parse_little.ml interp.cmi str_little.cmo
	ocamlc -c parse_little.ml

proof_sqrt.v : context_sqrt.v tail_sqrt.v sqrt.lil little
	./little -vcg-coq < sqrt.lil | cat context_sqrt.v - tail_sqrt.v \
           > proof_sqrt.v

test_vcg.lil : ex_int.lil little
	./little -static-analysis < ex_int.lil > test_vcg.lil 

clean : 
	rm -f *.vo interp.mli interp.ml parse_little.ml parse_little.mli\
        llex.ml *.cmo *.cmi little proof_sqrt.v test_vcg.lil

