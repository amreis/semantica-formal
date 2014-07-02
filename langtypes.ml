(** Module that contains the definitions for the types and AST syntax of
	the language and functions that operate on them *)

(** The available types for the ASTs of the language *)
type ty =
	TyNat					(** Nat (numbers) 			*)
	| TyBool				(** Bool (booleans) 	 	*)
	| TyArr of ty * ty		(** T1 -> T2 (functions) 	*)
	| TyId of string		(** X (type variables)		*)
	| TyList of ty			(** T1 list	(list type)  	*)

(** A type scheme is a pair, where the first element represents the names of
	the variables that are generalized, and thus must be replaced by new ones
	when instantiating the base type, that is the second component of the pair *)
type tyScheme =  TypeScheme of (string list) * ty

(** AST Syntax *)
type term = 
	TmZero								(** 0 						*)
	| TmTrue							(** true 					*)
	| TmFalse							(** false 					*)
	| TmSucc of term 					(** succ (t) 				*)
	| TmPred of term 					(** pred (t) 				*)
	| TmIsZero of term					(** iszero (t) 				*)
	| TmIf of term * term * term		(** if t1 then t2 else t3 	*)
	| TmAbs of string * ty * term		(** fn x:T => t 			*)
	| TmApp of term * term				(** (t1 t2) 				*)
	| TmVar of string					(** x 						*)
	(* EXTENSÃO : TIPAGEM IMPLÍCITA *)
	| TmImplAbs of string * term		(** fn x => t 				*)
	(* EXTENSÃO : LET POLIMÓRFICO *)
	| TmLet of string * term * term		(** let x = t1 in t2 		*)
	(* EXTENSÃO : LISTAS *)
	| TmNil								(** [] 						*)
	| TmCons of term * term				(** t1::t2 					*)
	| TmHead of term					(** hd (t1) 				*)
	| TmTail of term					(** tl (t1) 				*)
	| TmRaise							(** raise 					*)
	| TmTry of term * term				(** try t1 with t2 			*)
	| TmLetRec of string * ty * term * term	(** let rec x:T1->T2 = e1 in e2 *)
	| TmImplLetRec of string * term * term	(** let rec x = e1 in e2 *)
	
(** A context is a list of bindings between variable names and their types,
	or in this case, Type Schemes (for let polymorphism) *)
type context = (string * tyScheme) list
	
(** A constraint is something of the form T1 = T2, here represented by the
	pair (T1, T2) *)
type constr = (ty * ty)

(** A substitution is a list of mappings of the form T1 => T2, here represented
	by the pair (T1, T2) *)
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

(** Function that determines whether an AST corresponds to a <b>numeric</b> value
	or not *)
let rec isnumber (t : term) = 
	match t with
	TmZero -> true
	| TmSucc(t') -> isnumber t'
	| _ -> false
	
(** Function that determines whether an AST corresponds to a value or not *)
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
				
