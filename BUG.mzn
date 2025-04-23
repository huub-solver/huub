% Use this editor as a MiniZinc scratch book
 %%% Team 4 UU, courses 1DL442 and 1DL451, Assignment 1, 2023

include "diffn.mzn";

%% Parameters:
int: maxLen = sum(k in 1..n)(k); % The maximum length of the rectangle
int: n = 10;
array[1..n] of int: SquaresX = [5, 7, 9, 11, 13, 15, 17, 19, 21, 23];
array[1..n] of int: SquaresY = [3, 5, 7, 9, 11, 6, 8, 10, 12, 4];
%% Derived parameters:
% None

%% Decision variables:
% w = The width of the r ectangle
var n..50: w; 
% h = The length of the rectangle
var n..50: h;
% rec = The area of the bounding rectangle
var int: rec = w*h;

% X[n] = the x coordinate of the lower-left corner of square n
array [1..n] of var 0..100: X; %% = [11, 7, 6];
% Y[n] = the y coordinate of;;%%  %the lower-left corner of square n
array [1..n] of var 0..100: Y; %% = [2, 10, 5];
% No problem constraints are enforced by this choice of variables

%% Redundant decision variables:
% None

%% Channelling constraints:
% None

%% Problem constraints:
% Bounding the squares to be within the rectangle


constraint forall(i in 1..n) (X[i] <= w-SquaresX[i] /\ Y[i] <= h-SquaresY[i]);
% No overlapping of squares
constraint diffn(X, Y, SquaresX, SquaresY);

%% Implied constraints:
% None

%% Symmetry-breaking problem constraints:
constraint symmetry_breaking_constraint(2*X[n] < w /\ 2*Y[n] < h);
% None

% Minimize the rectangle area
solve minimize rec;

output ["w:\(w) h:\(h) X:\(X) Y:\(Y) rec: \(rec) squares: \(SquaresX)"];
