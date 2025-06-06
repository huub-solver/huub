predicate fzn_cumulative(
	array[int] of var int: s,
	array[int] of var int: d,
	array[int] of var int: r, 
	var int: b,
) =
	assert(
        index_set(s) == index_set(d) /\ index_set(s) == index_set(r),
        "cumulative: the 3 array arguments must have identical index sets",
	) /\ forall(i in index_set(d))(d[i] >= 0 /\ r[i] >= 0)
	  /\ if is_fixed(d) /\ is_fixed(r) /\ is_fixed(b) then
		    huub_cumulative(s, fix(d), fix(r), fix(b))
	    else
		    let {
                set of int: Tasks = {i | i in index_set(s) where ub(r[i]) > 0 /\ ub(d[i]) > 0};
                int: early = min([lb(s[i]) | i in Tasks]);
                int: late = max([ub(s[i]) + ub(d[i]) | i in Tasks]);
            } in (forall (t in early..late) (b >= sum (i in Tasks) ((s[i] <= t /\ t < s[i] + d[i]) * r[i])))
	    endif;

predicate huub_cumulative(array[int] of var int: s, array[int] of int: d, array[int] of int: r, int: b);
