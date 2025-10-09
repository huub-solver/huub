array[1..5] of var bool: x; 

constraint sum(x) = 3;  

solve :: bool_search(x, input_order, indomain_min, complete) satisfy;
