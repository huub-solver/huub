include "globals.mzn";

array[1..2] of var 1..1: posx;
array[1..2] of var 1..1: posy;

array[1..2] of var 4..4: sizex;
array[1..2] of var 4..4: sizey;

constraint diffn(posx, posy, sizex, sizey);

solve satisfy;

