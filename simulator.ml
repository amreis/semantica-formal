open Langtypes;;

let substFreeOccurrences (var : string)
						 (e : term)
						 (t : term)
						 (nxt : uvargen) = 
	let rec s v e t nxt = 
		match t with
		TmSucc(t1) ->
			(TmSucc(s v e t1 nxt), nxt)
		| TmPred(t1) ->
			(TmPred(s v e t1 nxt), nxt)
		| TmIsZero(t1) ->
			(TmIsZero(s v e t1 nxt), nxt)
		| TmIf(t1, t2, t3) ->
			(TmIf(s v e t1 nxt, 
				 s v e t2 nxt,
				 s v e t3 nxt), nxt)
		| TmAbs(x, ty, t1) when (x <> v) ->
			let NextUVar(z, nxt1) = nxt() in
			let (r1, nxt2) = s x TmVar(z) t1 nxt1 in
			let (r2, nxt3) = s v e r1 nxt2 in
			(TmAbs(z, ty, r2), nxt3)
		(** INCOMPLETE **)
		| x -> x
