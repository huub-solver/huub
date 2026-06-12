predicate huub_lex_less_int(array [int] of var int: x, array [int] of var int: y);
predicate fzn_lex_less_int(array [int] of var int: x, array [int] of var int: y) =
	huub_lex_less_int(x, y);
