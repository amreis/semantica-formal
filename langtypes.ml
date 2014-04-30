type ty =
	TyNat
	| TyBool
	| TyArr of ty * ty
	| TyId of string
	| TyList of ty
	
type info = string

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
	(* EXTENSÃO : LISTAS *)
	| TmCons of term * term
	| TmNil
	| TmHead of term
	| TmTail of term
	(* Falta: Exceções, Let Polimórfico *)
	(*
	| TmRaise
	| TmTry of term * term *)
type context = (string * ty) list
	
type constr = (ty * ty)

type subst = (ty * ty) list


