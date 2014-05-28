type ty =
	TyNat
	| TyBool
	| TyArr of ty * ty
	| TyId of string
	| TyList of ty
	
type info = string

type tyScheme =  TypeScheme of (string list) * ty

type term = 
	TmZero
	| TmTrue
	| TmFalse
	| TmSucc of term
	| TmPred of term
	| TmIsZero of term
	| TmIf of term * term * term
	| TmAbs of string * ty * term
	| TmApp of term * term
	| TmVar of string
	(* EXTENSÃO : TIPAGEM IMPLÍCITA *)
	| TmImplAbs of string * term
	(* EXTENSÃO : LET POLIMÓRFICO *)
	| TmLet of string * term * term
	(* EXTENSÃO : LISTAS *)
	| TmNil
	| TmCons of term * term
	| TmHead of term
	| TmTail of term
	| TmRaise
	| TmTry of term * term
	| TmLetRec of string * ty * term * term
	| TmImplLetRec of string * term * term
type context = (string * tyScheme) list
	
type constr = (ty * ty)

type subst = (ty * ty) list

let rec typeToString t = match t with
		TyNat -> "Nat"
		| TyBool -> "Bool"
		| TyId(var) -> var
		| TyList(t1) -> (typeToString t1) ^ " list"
		| TyArr(t1, t2) -> 
			"(" ^ (typeToString t1) ^ " -> " ^ (typeToString t2) ^ ")"

let printType (t : ty) : unit =  
	print_endline (typeToString t)
	
let rec termToString (t:term) = match t with
	| TmZero -> "0"
	| TmTrue -> "true"
	| TmFalse -> "false"
	| TmSucc(t1) -> "(succ " ^ (termToString t1) ^ ")"
	| TmPred(t1) -> "(pred " ^ (termToString t1) ^ ")"
	| TmIsZero(t1) -> "(iszero " ^ (termToString t1) ^ ")"
	| TmIf(t1,t2,t3) -> "(if " ^ (termToString t1) ^ " then " ^
							termToString t2 ^ " else " ^ termToString t3 ^ ")"
	| TmAbs(id,typ,t1) -> "(fn " ^ id ^ ":" ^ typeToString typ ^ " => " 
								^ termToString t1 ^ ")"
	| TmApp(t1, t2) -> "(" ^ termToString t1 ^ " " ^ termToString t2 ^ ")"
	| TmVar(id) -> id
	| TmImplAbs(id,t1) -> "(fn " ^ id ^ " => " ^ termToString t1 ^ ")"
	| TmLet(id, t1, t2) -> "(let " ^ id ^ " = " ^ termToString t1 ^ "\nin " ^
							termToString t2 ^ ")"
	| TmNil -> "[]"
	| TmCons(t1, t2) -> "(" ^ termToString t1 ^ "::" ^ termToString t2 ^ ")"
	| TmHead(t) -> "(hd " ^ termToString t ^ ")"
	| TmTail(t) -> "(tl " ^ termToString t ^ ")"
	| TmRaise -> "raise"
	| TmTry(t1, t2) -> "(try " ^ termToString t1 ^ " with " ^ termToString t2 ^ ")"
	| TmLetRec(id,ty,t1,t2) -> 
		"(let rec " ^ id ^ ":" ^ typeToString ty ^ " = " ^ termToString t1 ^
			" in " ^ termToString t2 ^ ")"
	| TmImplLetRec(id, t1, t2) ->
		"(let rec " ^ id ^ " = " ^ termToString t1 ^
			" in " ^ termToString t2 ^ ")"
let printTerm (t : term) =
	print_endline (termToString t)

(** Utilitary Type for generating new variables *)
type nextuvar = NextUVar of string * uvargenerator
	and uvargenerator = unit -> nextuvar
(** Function that generates two things: the new variable and the function
	that must be used to generate the next variable *)
let uvargen =
	let rec f n () = NextUVar("?X_" ^ string_of_int n, f (n+1))
	in f 0


let rec isnumber (t : term) = 
	match t with
	TmZero -> true
	| TmSucc(t') -> isnumber t'
	| _ -> false
let rec isvalue (t : term) = 
	isnumber t ||
		( match t with
			TmImplAbs(_,_) 	-> true
			| TmAbs(_,_,_) 	-> true
			| TmVar(_) 		-> true
			| TmNil 		-> true
			| TmTrue		-> true
			| TmFalse		-> true
			| TmCons(t1,t2) ->
				isvalue t1 && isvalue t2 
			| _ 			-> false)
				
