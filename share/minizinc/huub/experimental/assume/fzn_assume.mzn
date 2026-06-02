predicate huub_assume(array [int] of var bool: b ::promise_ctx_monotone);
predicate fzn_assume(array [int] of var bool: b ::promise_ctx_monotone) = huub_assume(b);
