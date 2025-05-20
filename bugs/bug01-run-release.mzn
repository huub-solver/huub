% Ume this editor as a MiniZinc scratch book
 %%% Team 4 UU, courses 1DL442 and 1DL451, Assignment 1, 2023

include "diffn.mzn";

%% Parameters:
int: n = 16; % The amount of squares
int: maxLen = 100; % The maximum length of the rectangle
array[1..n] of 1..n: Squares = [i | i in 1..n]; % Square[s] = dimension of square s (1x1, ..., nxn)
%% Derived parameters:
% None


%% Decision variables:
% w = The width of the r ectangle
var n..maxLen: w;
% h = The length of the rectangle
var n..maxLen: h;
% rec = The area of the bounding rectangle
var int: rec = w*h;

% X[n] = the x coordinate of the lower-left corner of square n
array [1..n] of var 0..maxLen: X;
% Y[n] = the y coordinate of the loer of square n
array [1..n] of var 0..maxLen: Y;
% No problem constraints are enforced by this choice of variables

%% Redundant decision variables:
% None

%% Channelling constraints:
% None

%% Problem constraints:
% Bounding the squares to be within the rectangle

constraint forall(i in 1..n) (X[i] <= w-Squares[i] /\ Y[i] <= h-Squares[i]);
% No overlapping of squares
constraint diffn(X, Y, Squares, Squares);

%% Implied constraints:
% None

%% Symmetry-breaking problem constraints:
constraint symmetry_breaking_constraint(2*X[n] < w /\ 2*Y[n] < h);
% None

% Minimize the rectangle area
solve minimize rec;

output ["w:\(w) h:\(h) X:\(X) Y:\(Y) rec: \(rec) squares: \(Squares)"];
