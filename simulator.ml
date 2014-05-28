open Langtypes;;


(* Replace v with e in t *)
let substFreeOccurrences (v : string) (e : term) (t : term) (nxt : uvargenerator) =
	let rec s (v:string) (e:term) (t:term) (nxt:uvargenerator)  : term * uvargenerator = 
	match t with
		TmIf(t1, t2, t3) ->
			let (r1, nxt1) = s v e t1 nxt in
			let (r2, nxt2) = s v e t2 nxt1 in
			let	(r3, nxt3) = s v e t3 nxt2 in
			(TmIf(r1,r2,r3), nxt3)
		| TmSucc(t1) -> 
			let (r1, nxt1) = s v e t1 nxt in
			(TmSucc(r1), nxt1)
		| TmPred(t1) -> 
			let (r1, nxt1) = s v e t1 nxt in
			(TmPred(r1), nxt1)
		| TmIsZero(t1) -> 
			let (r1, nxt1) = s v e t1 nxt in
			(TmIsZero(r1), nxt1)
		| TmVar(x) ->
			((if x = v then e else TmVar(x)), nxt)
		| TmAbs(id, ty, term) when (id <> v) ->

			let NextUVar(z, nxt1) = nxt() in
			let (r1, nxt2) = s id (TmVar z) term nxt1 in
			let (r2, nxt3) = s v e r1 nxt2 in
			(TmAbs(z, ty, r2), nxt3)

		| TmImplAbs(id, term) when (id <> v) ->
			let NextUVar(z, nxt1) = nxt() in
			let (r1, nxt2) = s id (TmVar z) term nxt1 in
			let (r2, nxt3) = s v e r1 nxt2 in
			(TmImplAbs(z, r2), nxt3)

		| TmApp(t1, t2) ->
			let (r1, nxt1) = s v e t1 nxt in
			let (r2, nxt2) = s v e t2 nxt1 in
			(TmApp(r1,r2), nxt2)

		| TmLet(id, t1, t2) when (id <> v) ->
			let NextUVar(z, nxt1) = nxt() in
			let (r1, nxt2) = s v e t1 nxt1 in
			let (r2, nxt3) = s id (TmVar z) t2 nxt2 in
			let (r3, nxt4) = s v e r2 nxt3 in
			(TmLet(z, r1, r3), nxt4)

		| TmCons(t1, t2) ->
			let (r1, nxt1) = s v e t1 nxt in
			let (r2, nxt2) = s v e t2 nxt1 in
			(TmCons(r1,r2), nxt2)
		| TmHead(t1) -> 
			let (r1, nxt1) = s v e t1 nxt in
			(TmHead(r1), nxt1)
		| TmTail(t1) ->
			let (r1, nxt1) = s v e t1 nxt in
			(TmTail(r1), nxt1)
		| TmTry(t1, t2) ->
			let (r1, nxt1) = s v e t1 nxt in
			let (r2, nxt2) = s v e t2 nxt1 in
			(TmTry(r1, r2), nxt2)

		| TmLetRec(id, ty, t1, t2) when (id <> v) ->
			let NextUVar(z, nxt1) = nxt() in
			let (r1, nxt2) = s id (TmVar z) t1 nxt1 in
			let (r2, nxt3) = s v e r1 nxt2 in
			let (r3, nxt4) = s id (TmVar z) t2 nxt3 in
			let (r4, nxt5) = s v e r3 nxt4 in
			(TmLetRec(z, ty, r2, r4), nxt5)
		| TmImplLetRec(id, t1, t2) when (id <> v) ->
			let NextUVar(z, nxt1) = nxt() in
			let (r1, nxt2) = s id (TmVar z) t1 nxt1 in
			let (r2, nxt3) = s v e r1 nxt2 in
			let (r3, nxt4) = s id (TmVar z) t2 nxt3 in
			let (r4, nxt5) = s v e r3 nxt4 in
			(TmImplLetRec(z, r2, r4), nxt5)
		| x -> (x, nxt)
	in
	s v e t nxt
exception NoRuleApplies;;


let rec step (t : term) (nxt : uvargenerator) : (term * uvargenerator) = 
	match t with
		TmIf(TmRaise, _, _) -> (TmRaise, nxt)
		| TmIf(TmTrue, t2, _) -> (t2, nxt)
		| TmIf(TmFalse, _, t3) -> (t3, nxt)
		| TmIf(t1, t2, t3) ->
			let (t1', nxt1) = step t1 nxt in
			(TmIf(t1', t2, t3), nxt1)
		| TmSucc(TmRaise) -> (TmRaise, nxt)
		| TmSucc(t1) ->
			let (t1', nxt1) = step t1 nxt in 
			(TmSucc(t1'), nxt1)
		| TmPred(TmRaise) -> (TmRaise, nxt)
		| TmPred(TmZero) -> (TmZero, nxt)
		| TmPred(TmSucc(nv)) when (isnumber nv) ->
			(nv, nxt)
		| TmPred(t) ->
			let (t', nxt1) = step t nxt in
			(TmPred(t'), nxt1)
		| TmIsZero(TmRaise) -> (TmRaise, nxt)
		| TmIsZero(TmZero) -> (TmTrue, nxt)
		| TmIsZero(TmSucc(nv)) when (isnumber nv) -> (TmFalse, nxt)
		| TmIsZero(t) -> 
			let (t', nxt1) = step t nxt in
			(TmIsZero(t'), nxt1)
		| TmApp(TmRaise, _) -> (TmRaise, nxt)
		| TmApp(t1, TmRaise) when (isvalue t1) -> (TmRaise, nxt)
		| TmApp(t1, t2) when (isvalue t1 && isvalue t2) -> 
		begin 
			match t1 with
			TmAbs(id, _, body) -> 
				substFreeOccurrences id t2 body nxt				
			| TmImplAbs(id, body) ->
				substFreeOccurrences id t2 body nxt
			| _ -> raise NoRuleApplies
		end
		| TmApp(t1, t2) when (isvalue t1) ->
			let (t2', nxt1) = step t2 nxt in
			(TmApp(t1, t2'), nxt1)
		| TmApp(t1, t2) ->
			let (t1', nxt1) = step t1 nxt in
			(TmApp(t1', t2), nxt1)
		| TmCons(TmRaise, _) -> (TmRaise, nxt)
		| TmCons(v, TmRaise) when (isvalue v) -> (TmRaise, nxt)
		| TmCons(v, t2) when (isvalue v) ->
			let (t2', nxt1) = step t2 nxt in
			(TmCons(v, t2'), nxt1)
		| TmCons(t1, t2) ->
			let (t1', nxt1) = step t1 nxt in
			(TmCons(t1', t2), nxt1)
		| TmHead(TmNil) -> (TmRaise, nxt)
		| TmHead(TmRaise) -> (TmRaise, nxt)
		| TmHead(v) when (isvalue v) ->
		begin
			match v with
			TmCons(f, _) -> (f, nxt)
			| _ -> raise NoRuleApplies
		end
		| TmHead(t) -> 
			let (t', nxt1) = step t nxt in
			(TmHead(t'), nxt1)
		| TmTail(TmNil) -> (TmRaise, nxt)
		| TmTail(TmRaise) -> (TmRaise, nxt)
		| TmTail(v) when (isvalue v) ->
		begin
			match v with
			TmCons(_, r) -> (r, nxt)
			| _ -> raise NoRuleApplies
		end
		| TmTail(t) -> 
			let (t', nxt1) = step t nxt in
			(TmTail(t'), nxt1)
		| TmTry(TmRaise, t2) -> (t2, nxt)
		| TmTry(v, t2) when (isvalue v) -> (v, nxt)
		| TmTry(t1, t2) -> 
			let (t1', nxt1) = step t1 nxt in
			(TmTry(t1', t2), nxt1)
		| TmLet(id, TmRaise, _) -> (TmRaise, nxt)
		| TmLet(id, v, t2) when (isvalue v) ->
			substFreeOccurrences id v t2 nxt
		| TmLet(id, t1, t2) ->
			let (t1', nxt1) = step t1 nxt in
			(TmLet(id, t1', t2), nxt1)
		| TmLetRec(id, ty, TmRaise, _) -> (TmRaise, nxt)
		| TmLetRec(id, ty, v, e2) when (isvalue v)->
		(match ty with
			TyArr(ty1,ty2) ->
			( match v with
				TmAbs(y, tyFun, e1) ->
					substFreeOccurrences id (TmAbs(y, ty1, TmLetRec(id, ty, v, e1))) e2 nxt
				| TmImplAbs(y, e1) ->
					substFreeOccurrences id (TmImplAbs(y, TmLetRec(id, ty, v, e1))) e2 nxt
				| _ -> raise NoRuleApplies
			)
			| _ -> raise NoRuleApplies
		)
		| TmLetRec(id, ty, t1, t2) ->
			let (t1', nxt1) = step t1 nxt in
			(TmLetRec(id, ty, t1', t2), nxt1)
		| TmImplLetRec(id, TmRaise, _) -> (TmRaise, nxt)
		| TmImplLetRec(id, v, t2) when (isvalue v) ->
		(match v with
			TmAbs(y, tyFun, f) ->
			(match tyFun with
				TyArr(ty1,ty2) ->
				substFreeOccurrences id (TmAbs(y, ty1, TmImplLetRec(id, v, f))) t2 nxt
				| _ -> raise NoRuleApplies
			)
			| TmImplAbs(y, f) ->
				substFreeOccurrences id (TmImplAbs(y, TmImplLetRec(id, v, f))) t2 nxt
			| _ -> raise NoRuleApplies
		)
		| TmImplLetRec(id, t1, t2) ->
			let (t1', nxt1) = step t1 nxt in
			(TmImplLetRec(id, t1', t2), nxt1)
		| _ -> raise NoRuleApplies
		
let discard (s:string) : unit = ()
let rec eval (t : term) (nxt : uvargenerator) =
	try
		printTerm t; discard(input_line stdin) ;
		let (t', nxt1) = step t nxt in
		eval t' nxt1
	with
		NoRuleApplies -> t
