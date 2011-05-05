%{
  open Big_int
  open String
  open Str_little
  open Str

(* Making Coq data. *)

let big_int2 = big_int_of_int 2

let z_of_big_int n =
    let rec f n = if eq_big_int n unit_big_int then Interp.XH 
                else let q,r = quomod_big_int n big_int2 in
                  if eq_big_int r unit_big_int then Interp.XI(f q)
                  else Interp.XO(f q) in
  if eq_big_int n zero_big_int then Interp.Z0 else Interp.Zpos(f n)

let p a b = Interp.Pair(a, b)
let c a b = Interp.Cons(a, b)
let nil = Interp.Nil

let rec mk_precs l i =
 match l with [] -> i | a :: tl -> Interp.Prec(a, mk_precs tl i)

%}
%token VARIABLES IN END WHILE DO DONE ASSIGN PLUS MINUS COMMA CONJ BANG
%token SEMICOLUMN OPEN CLOSE BOPEN BCLOSE SKIP LT SOPEN SCLOSE MINFTY PINFTY
%token <Big_int.big_int> NUM
%token <string> ID
%left PLUS
%right CONJ
%type <(string,Interp.z)Interp.prod Interp.list*string Interp.a_instr0> main
%type <string Interp.a_instr0> inst
%start main main_intervals inst_with_post
%type <Interp.z> num
%type <string> identifier
%type <(string,(Interp.ext_Z,Interp.ext_Z)Interp.prod)Interp.prod Interp.list*string Interp.a_instr0>main_intervals
%type <string Interp.a_instr0*string Interp.assert0> inst_with_post
%%
main : VARIABLES environment IN inst END { ($2, $4) }
;
main_intervals : VARIABLES interval_environment IN inst END  { ($2,$4) }
num : NUM { z_of_big_int $1 } | MINUS NUM {Interp.Z.opp (z_of_big_int $2)}
;
identifier : ID { $1 }
;
variable_value : identifier num { p $1 $2 }
;
bound : num {Interp.CZ $1} | MINFTY {Interp.Minfty} | PINFTY {Interp.Pinfty}
;
variable_interval : identifier bound bound {p $1 (p $2 $3)}
;
interval_environment : { nil}
| variable_interval interval_environment {c $1 $2}
;
environment : { nil }
| variable_value environment { c $1 $2 }
;
inst: elem_inst {$1}
|  elem_inst SEMICOLUMN inst { Interp.A_sequence($1,$3) }
;
elem_inst : elem_inst0 {$1}
| SOPEN l_assert SCLOSE elem_inst {Interp.Prec($2,$4)}
;

elem_inst0 : BOPEN inst BCLOSE { $2 } 
|  SKIP { Interp.A_skip }
|  WHILE b_exp DO inst DONE 
     {match $4 with Interp.Prec(a,i) -> Interp.A_while($2,a, i)
         | Interp.A_sequence(Interp.Prec(a,i),j) ->
           Interp.A_while($2, a, Interp.A_sequence(i, j))
         | it -> Interp.A_while($2, false_assert, it)}
|  identifier ASSIGN exp { Interp.A_assign($1,$3) }
;
inst_with_post : 
  elem_inst SOPEN l_assert SCLOSE {($1,$3)}
| elem_inst SEMICOLUMN inst_with_post 
   {let a,b = $3 in Interp.A_sequence($1,a), b }
;
exp: num { Interp.Anum($1) }
|    identifier { Interp.Avar($1) }
|    exp PLUS exp { Interp.Aplus($1, $3); }
|    OPEN exp CLOSE { $2 }
;
b_exp: exp LT exp { Interp.Blt($1, $3) }
;
elem_assert : b_exp {Interp.A_b($1)}
|   identifier OPEN l_exp CLOSE {Interp.Pred($1, $3)}
|   BANG elem_assert {Interp.A_not($2)}
;
l_assert : elem_assert {$1}
| elem_assert CONJ l_assert {Interp.A_conj($1,$3)}
;
l_exp : l_exp1 {$1}
| {Interp.Nil}
;
l_exp1 : exp { Interp.Cons($1, Interp.Nil)}
| exp COMMA l_exp1 {Interp.Cons($1, $3)}
;
%%
