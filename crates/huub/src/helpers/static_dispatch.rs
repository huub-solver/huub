macro_rules! static_dispatch {
	// Entry
  (
	  [ $( $ty:tt |> $e:expr ),+ $(,)? ], | $($x:ident),+ | $body:expr
  ) => {
	  static_dispatch!(@recur [ $( $ty |> $e ),+ ] ; [] ; | $($x),+ | $body)
  };
  // Recursive case: still have at least one enum to match
  (@recur  [ IntView |> $head:expr $(, $ty:tt |> $tail:expr )* ] ; [ $($bound:ident),* ] ;
	  | $($x:ident),+ | $body:expr
  ) => {
	  match $head.0 {
		  $crate::solver::IntViewInner::Const(v) => {
			  static_dispatch!(
				  @recur
				  [ $( $ty |> $tail ),* ] ;
				  [ $($bound,)* v ] ;
				  | $($x),+ | $body
			  )
		  }
		  $crate::solver::IntViewInner::Linear(lin) if lin.scale.get() == 1 && lin.offset == 0 => {
				let view = lin.var;
			  static_dispatch!(
				  @recur
				  [ $( $ty |> $tail ),* ] ;
				  [ $($bound,)* view ] ;
				  | $($x),+ | $body
			  )
		  }
		  $crate::solver::IntViewInner::Linear(lin) if lin.scale.get() == 1 => {
				let view = $crate::views::offset_view::OffsetView::new(lin.offset, lin.var);
			  static_dispatch!(
				  @recur
				  [ $( $ty |> $tail ),* ] ;
				  [ $($bound,)* view ] ;
				  | $($x),+ | $body
			  )
		  }
		  $crate::solver::IntViewInner::Linear(lin) => {
			  static_dispatch!(
				  @recur
				  [ $( $ty |> $tail ),* ] ;
				  [ $($bound,)* lin ] ;
				  | $($x),+ | $body
			  )
		  }
			$crate::solver::IntViewInner::Bool(view) => {
			  static_dispatch!(
				  @recur
				  [ $( $ty |> $tail ),* ] ;
				  [ $($bound,)* view ] ;
				  | $($x),+ | $body
			  )
		  }
	  }
  };
  (@recur  [ VecIntView |> $head:expr $(, $ty:tt |> $tail:expr )* ] ; [ $($bound:ident),* ] ;
	  | $($x:ident),+ | $body:expr
  ) => {{
  	let mut const_ = 0;
   	let mut bool_ = 0;
    let mut int = 0;
    let mut offset = 0;
    let mut scale = 0;
    let orig: Vec<$crate::solver::IntView> = $head;
    for view in &orig {
      match view.0 {
        $crate::solver::IntViewInner::Const(_) => const_ += 1,
        $crate::solver::IntViewInner::Bool(_) => bool_ += 1,
        $crate::solver::IntViewInner::Linear(lin) if lin.scale.get() == 1 && lin.offset == 0 => int +=1,
        $crate::solver::IntViewInner::Linear(lin) if lin.scale.get() == 1 => offset += 1,
        $crate::solver::IntViewInner::Linear(_) => scale += 1,
      }
    }
    match (const_, bool_, int, offset, scale) {
	    (_, 0, 0, 0, 0) => {
				let views: Vec<_> = orig.into_iter().map(|v| {let $crate::solver::IntViewInner::Const(c) = v.0 else {unreachable!()}; c}).collect();
        static_dispatch!(
          @recur
          [ $( $ty |> $tail ),* ] ;
          [ $($bound,)* views ] ;
          | $($x),+ | $body
        )
	    }
	    (0, _, 0, 0, 0) => {
				let views: Vec<_> = orig.into_iter().map(|v| {let $crate::solver::IntViewInner::Bool(view) = v.0 else {unreachable!()}; view}).collect();
        static_dispatch!(
          @recur
          [ $( $ty |> $tail ),* ] ;
          [ $($bound,)* views ] ;
          | $($x),+ | $body
        )
	    }
	    (0, 0, _, 0, 0) => {
				let views: Vec<_> = orig.into_iter().map(|v| {let $crate::solver::IntViewInner::Linear(view) = v.0 else {unreachable!()}; view.var}).collect();
        static_dispatch!(
          @recur
          [ $( $ty |> $tail ),* ] ;
          [ $($bound,)* views ] ;
          | $($x),+ | $body
        )
	    }
	    (0, 0, _, _, 0) => {
				let views: Vec<_> = orig.into_iter().map(|v| {let $crate::solver::IntViewInner::Linear(view) = v.0 else {unreachable!()}; $crate::views::offset_view::OffsetView::new(view.offset, view.var)}).collect();
        static_dispatch!(
          @recur
          [ $( $ty |> $tail ),* ] ;
          [ $($bound,)* views ] ;
          | $($x),+ | $body
        )
	    }
	    (0, 0, _, _, _) => {
				let views: Vec<_> = orig.into_iter().map(|v| {let $crate::solver::IntViewInner::Linear(view) = v.0 else {unreachable!()}; view}).collect();
        static_dispatch!(
          @recur
          [ $( $ty |> $tail ),* ] ;
          [ $($bound,)* views ] ;
          | $($x),+ | $body
        )
	    }
	    _ => {
        static_dispatch!(
          @recur
          [ $( $ty |> $tail ),* ] ;
          [ $($bound,)* orig ] ;
          | $($x),+ | $body
        )
	    }
    }
  }};
  (@recur  [ BoolView |> $head:expr $(, $ty:tt |> $tail:expr )* ] ; [ $($bound:ident),* ] ;
	  | $($x:ident),+ | $body:expr
  ) => {
	  match $head.0 {
		  $crate::solver::BoolViewInner::Const(v) => {
			  static_dispatch!(
				  @recur
				  [ $( $ty:ty |> $tail ),* ] ;
				  [ $($bound,)* v ] ;
				  | $($x),+ | $body
			  )
		  }
		  $crate::solver::BoolViewInner::Lit(v) => {
			  static_dispatch!(
				  @recur
				  [ $( $ty:ty |> $tail ),* ] ;
				  [ $($bound,)* v ] ;
				  | $($x),+ | $body
			  )
		  }
	  }
  };
  // Base case: no enums left — execute the body with the collected values
  (@recur [ ] ; [ $($vals:ident),* ] ;
	  | $($x:ident),+ | $body:expr
  ) => {{
	  let ( $($x),* ) = ( $($vals),* );
	  $body
  }};
}

pub(crate) use static_dispatch;
