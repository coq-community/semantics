{
  open Parse_little;;
  exception Eof;;
  exception Lex_error of int;;
  let count = ref 0;;
}
rule token = parse
  [ ' ' '\t' ] {token lexbuf}
| ['\n'] {count:=!count+1; token lexbuf}
| ":=" {ASSIGN} | ";" {SEMICOLUMN} | "/\\" {CONJ} | "!" {BANG}
| "while" {WHILE} | "do" {DO} | "done" {DONE} | "[" {SOPEN} | "]" {SCLOSE}
| "variables" {VARIABLES} | "in" {IN} | "end" {END} | "<" {LT} | "-" {MINUS}
| "," {COMMA} | "(" {OPEN} | ")" {CLOSE} | "skip" {SKIP} | "+" {PLUS}
| "{" {BOPEN} | "}" {BCLOSE} | "minfty" {MINFTY} | "pinfty" {PINFTY}
| ['a'-'z''A'-'Z''_']['a'-'z' 'A'-'Z' '0'-'9' '_']* {ID(Lexing.lexeme lexbuf)}
| ['0'-'9']+ {NUM(Big_int.big_int_of_string(Lexing.lexeme lexbuf))}
| _ {raise (Lex_error(Lexing.lexeme_start lexbuf))}
| _ {raise Eof}

