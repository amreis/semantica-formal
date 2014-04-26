type ty =
	TyNat
	| TyBool
	| TyArr of ty * ty
	| TyId of string
	| TyList of ty
	
type info = string

type term = 
	TmZero of info
	| TmTrue of info
	| TmFalse of info
	| TmSucc of info * term
	| TmPred of info * term
	| TmIsZero of info * term
	| TmIf of info * term * term * term
	| TmAbs of info * string * ty * term
	| TmApp of info * term * term
	| TmVar of info * string
	(* EXTENSÃO : TIPAGEM IMPLÍCITA *)
	| TmImplAbs of info * string * term
	(* EXTENSÃO : LISTAS *)
	| TmCons of info * term * term
	| TmNil of info
	| TmHead of info * term (***)
	| TmTail of info * term (***)
	| TmIsNil of info * term  (***)

type context = (string * ty) list
	
type constr = (ty * ty)

type subst = (ty * ty) list


