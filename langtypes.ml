type ty =
	TyNat
	| TyBool
	| TyArr of ty * ty
	| TyId of string
	
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
	| TmImplAbs of info * string * term
	| TmApp of info * term * term
	| TmVar of info * string

type context = (string * ty) list
	
type constr = (ty * ty)

type subst = (ty * ty) list


