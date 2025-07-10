predicate fzn_disjunctive_strict(
	array[int] of var int: s,
	array[int] of var int: d
) =
	forall(i in index_set(d))(d[i] >= 0)
	/\ if is_fixed(d) then
		huub_disjunctive_strict(s, fix(d))
	else
		forall(i, j in index_set(d) where i < j) (
			s[i] + d[i] <= s[j] \/ s[j] + d[j] <= s[i]
		)
	endif;

predicate huub_disjunctive_strict(array[int] of var int: s, array[int] of int: d);

%------------------------------------------------------------------------------%
% Annotations for the disjunctive constraint
%------------------------------------------------------------------------------%

/** @group Huub.annotations Enforce the edge finding algorithm to be used in the propagator of the disjunctive constraint */
annotation edge_finding;

/** @group Huub.annotations Enforce the not-last algorithm to be used in the propagator of the disjunctive constraint */
annotation not_last;

/** @group Huub.annotations Enforce the detectable precedence algorithm to be used in the propagator of the disjunctive constraint */
annotation detectable_precedence;
