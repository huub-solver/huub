% Use this editor as a MiniZinc scratch book
 %%% Team 4 UU, courses 1DL442 and 1DL451, Assignment 1, 2023

include "diffn.mzn";

%% Parameters:
int: n = 3; % The amount of squares
int: maxLen = sum(k in 1..n)(k); % The maximum length of the rectangle
array[1..n] of int: SquaresX = [3, 4, 5]; % Square[s] = dimension of square s (1x1, ..., nxn)
array[1..n] of int: SquaresY = [10, 2, 2]; % Square[s] = dimension of square s (1x1, ..., nxn)
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
array [1..n] of var 6..15: X; %% = [11, 7, 6];
% Y[n] = the y coordinate of;;%%  %the lower-left corner of square n
array [1..n] of var 2..12: Y; %% = [2, 10, 5];
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
