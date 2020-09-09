% --- INCLUDES ------------- %
include "globals.mzn";

% --- ONLINE MINIZINC ------ %
int: now;
enum GC = {NO_GC, SIMPLE_GC, ADVANCED_GC};
GC: GC_MODE; % Whether realizations, garbage, and aggregation analysis will be used. 
             % Provided (previous) aggregations will still be used even if false.
int: incr = 408;

% --- TABLE OF CONTENTS ---- %
%   1. Enums
%   2. Data Parameters
%   3. Variables
%   4. Realizations
%   5. Constraints
%   6. Aggregations
%   7. Garbage Nomination
%   8. Garbage Omission
%   9. Outputs
%  10. Online MiniZinc Library

% -------------------------- %
% --- ENUMS ---------------- %
% -------------------------- %

% - Sol Enums ----- %
enum sol_J; % old jobs

% - Enums --------- %
enum M;          % machines
set of M: T = M; % tasks per machine

enum new_J; % new jobs
enum J = anon_enum(card(agg_sol_J) + card(new_J));

% - Enum Mappings - %
J: new2J(new_J: j) = J[card(agg_sol_J) + card({i | i in new_J where i <= j})];

new_J: J2new(J: j) = {i | i in new_J where new2J(i) = j}[1];

J: sol2J(agg_sol_J: j) = J[card({i | i in agg_sol_J where i <= j})];

agg_sol_J: J2sol(J: j) = {i | i in agg_sol_J where sol2J(i) = j}[1];

% - Enum Map Checks - %
test is_sol(set of $$E: e, $$E: i) =
  if e = J
    then e[i] in {sol2J(j) | j in agg_sol_J}
    else assert(false, "unsupported is_sol call \(e) \(i), \(e[i])")
  endif;

% -------------------------- %
% --- DATA PARAMETERS ------ %
% -------------------------- %

% - Sol Data - %
array [sol_J, M] of int: sol_dur;
array [sol_J, T] of M: sol_mach;

% - Data ----- %
array [new_J, M] of int: new_dur;
array [J, M] of int: dur = array2d(J, T, [ if is_sol(J, j)
                                           then sol_dur[J2sol(j),t]
                                           else new_dur[J2new(j),t]
                                         endif | j in J, t in T ]);

array [new_J, T] of M: new_mach;
array [J, T] of M: mach = array2d(J, T, [ if is_sol(J, j)
                                            then sol_mach[J2sol(j),t]
                                            else new_mach[J2new(j),t]
                                          endif | j in J, t in T ]);


% -------------------------- %
% --- VARIABLES ------------ %
% -------------------------- %

% - Sol Variables - %
array [sol_J, T] of int: sol_start;

% - Variables - %
array [J, T] of var 0..now+sum(dur): start;

% -------------------------- %
% --- REALIZATIONS --------- %
% -------------------------- %

int: LJ = arg_max([ bool2int( exists(i in T) (sol_start[j,i] + sol_dur[j,sol_mach[j,i]] > now)) | j in sol_J ] ++ [1]);

bool: realized_J(sol_J: j) = if GC_MODE = SIMPLE_GC
                               then j < LJ
                             elseif GC_MODE = ADVANCED_GC
                               then forall (t in T) (realized_dur_J(j,t))
                                 /\ forall (t in T) (realized_mach_J(j,t))
                                 /\ forall (t in T) (realized_start_J(j,t))
                               else false
                             endif;
                             
bool: realized(set of $$E: e, $$E: i) =
  if GC_MODE = NO_GC
    then false
    else realized_J(sol_J[i])
  endif;

% - Par Realizations -- %
bool: realized_dur_J(sol_J: j, T: t) = sol_start[j,t] + sol_dur[j,sol_mach[j,t]] <= now;
bool: realized_mach_J(sol_J: j, T: t) = sol_start[j,t] + sol_dur[j,sol_mach[j,t]] <= now;

% - Var Realizations -- %
bool: realized_start_J(sol_J: j, T: t) = sol_start[j,t] + sol_dur[j,sol_mach[j,t]] <= now;

% - Realization Sets -- %
set of sol_J: REALIZED_J = {j | j in sol_J where realized(sol_J, j)};

% -------------------------- %
% --- CONSTRAINTS ---------- %
% -------------------------- %

% - Problem Constraints - %

%% No overlap of tasks within a jobs
constraint forall (j in J, t in T where t != max(T))
 ( start[j,t] + dur[j,mach[j,t]] <= start[j,enum_next(T, t)] );

%% No overlap of jobs on a machine
constraint if card(J) > 0 /\ card(T) > 0
             then forall (m in M)
                    ( disjunctive([start[j,t] | j in J, t in T where mach[j,t] = m],
                                  dur[..,m]) )
             else true
           endif;

% - Overlap Constraints - %

%% start is time variable
constraint forall (j in J, t in T)
 ( if is_sol(J, j)
   /\ sol_start[J2sol(j),t] < now
     then start[j,t] = sol_start[J2sol(j),t]
     else start[j,t] >= now
   endif );

% -------------------------- %
% --- OBJECTIVE ------------ %
% -------------------------- %

var int: makespan;

constraint forall (j in J)
 ( start[j,max(T)] + dur[j,mach[j,max(T)]] <= makespan );

solve 
  :: int_search(start, dom_w_deg, indomain_min)
  minimize makespan;

% -------------------------- %
% --- AGGREGATION ---------- %
% -------------------------- %

% NONE

% -------------------------- %
% --- GARBAGE NOMINATION --- %
% -------------------------- %

% % - Forall Nomination 1D - %
set of $$E: agg_idx_forall(set of $$E: e) =
  {i | i in index_set(e) where not(realized(e, i))};

% -------------------------- %
% --- GARBAGE OMISSION ----- %
% -------------------------- %

set of sol_J: agg_sol_J = agg_idx_forall(sol_J);
                                                                                                   
bool: garbage(sol_J: j) = not(j in agg_sol_J);

% --- OUTPUT --------------- %

 output ["--START-SOL-OUTPUT--"
     ++ "\nnow = \(now+incr);"
     ++ "\nsol_J = \(J);"
     ++ "\nsol_dur = array2d(sol_J, M, \(dur));"
     ++ "\nsol_mach = array2d(sol_J, T, \(mach));"
     ++ "\nsol_start = array2d(sol_J, T, \(start));"
     ++ "--END-SOL-OUTPUT--"
     ++ "\n"
     ++ "--START-OBJ-OUTPUT--\(makespan)--END-OBJ-OUTPUT--"
     ++ "--START-GCJ-OUTPUT--\(card(sol_J) - card(agg_sol_J))--END-GCJ-OUTPUT--"
 ];


% --- Online MZN Library --- %

test has_sol(opt $$E: sol_x) =
  occurs(sol_x);

test has_sol(array[$$E] of $$A: sol_x, $$E: i) =
  i in index_set(sol_x);

test has_sol(array[$$E] of set of $$A: sol_x, $$E: i) =
  i in index_set(sol_x);

test has_sol(array[$$E, $$F] of $$A: sol_x, $$E: i1, $$F: i2) =
  i1 in index_set_1of2(sol_x) /\
  i2 in index_set_2of2(sol_x);

test has_sol(array[$$E, $$F, $$G] of $$A: sol_x, $$E: i1, $$F: i2, $$G: i3) =
  i1 in index_set_1of3(sol_x) /\
  i2 in index_set_2of3(sol_x) /\
  i3 in index_set_3of3(sol_x);
