% --- INCLUDES ------------- %
include "globals.mzn";

% --- ONLINE MINIZINC ------ %
int: now;
bool: ENABLE_GARBAGE; % Whether realizations, garbage, and aggregation analysis will be used. 
                      % Provided (previous) aggregations will still be used even if false.
int: incr = 50;
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
enum sol_V; % old vehicles
enum sol_C; % old customers
enum sol_N; % = anon_enum(card(sol_V)*2+card(sol_C));

% - Enums --------- %
enum new_V; % new vehicles
enum V = anon_enum(card(agg_sol_V) + card(new_V));

enum new_C; % new customers
enum C = anon_enum(card(agg_sol_C) + card(new_C));

enum new_N = anon_enum(card(new_V)*2+card(new_C));
enum N = anon_enum(card(V)*2+card(C)); % nodes

% - Enum Mappings - %
V: new2V(new_V: v) = V[card(agg_sol_V) + card({i | i in new_V where i <= v})];
C: new2C(new_C: c) = C[card(agg_sol_C) + card({i | i in new_C where i <= c})];
new_V: V2new(V: v) = {i | i in new_V where new2V(i) = v}[1];
new_C: C2new(C: c) = {i | i in new_C where new2C(i) = c}[1];

V: sol2V(agg_sol_V: v) = V[card({i | i in agg_sol_V where i <= v})];
C: sol2C(agg_sol_C: c) = C[card({i | i in agg_sol_C where i <= c})];
agg_sol_V: V2sol(V: v) = {i | i in agg_sol_V where sol2V(i) = v}[1];
agg_sol_C: C2sol(C: c) = {i | i in agg_sol_C where sol2C(i) = c}[1];

N: sol2N(agg_sol_N: n) = let  
  { int: i = card({ i | i in agg_sol_N where i <= n });
    int: sv = card(agg_sol_V);
    int: ev = card(agg_sol_V)*2;
  } in if i > ev
         then N[card(V)*2+i-ev]
       elseif i > sv
         then N[card(V)+i-sv]
         else N[i]
    endif;
agg_sol_N: N2sol(N: n) = {i | i in agg_sol_N where sol2N(i) = n}[1];

N: new2N(new_N: n) = let  
  { int: i = card({ i | i in new_N where i <= n });
    int: sv = card(new_V);
    int: ev = card(new_V)*2;
  } in if i > ev
         then N[card(agg_sol_C)+card(V)*2+i-ev]
       elseif i > sv
         then N[card(agg_sol_V)+card(V)+i-sv]
         else N[card(agg_sol_V)+i]
    endif;
new_N: N2new(N: n) = {i | i in new_N where new2N(i) = n}[1];
  
sol_N: sol_SV2N(sol_V: v) = sol_N[                  card({i | i in sol_V where i <= v})];
sol_N: sol_EV2N(sol_V: v) = sol_N[card(sol_V)     + card({i | i in sol_V where i <= v})];
sol_N: sol_C2N(sol_C: c) =  sol_N[card(sol_V) * 2 + card({i | i in sol_C where i <= c})];
%sol_V: sol_N2SV(sol_N: n) = {v | v in sol_V where sol_SV2N(v) = n}[1];
%sol_V: sol_N2EV(sol_N: n) = trace("\n\n n = \(n), sol_V = \(sol_V), sol_N = \(sol_N))", {v | v in sol_V where sol_EV2N(v) = n}[1]);
sol_V: sol_N2V(sol_N: n) = {v | v in sol_V where sol_SV2N(v) = n \/ sol_EV2N(v) = n}[1];
sol_C: sol_N2C(sol_N: n) = {c | c in sol_C where sol_C2N(c) = n}[1];

new_N: new_SV2N(new_V: v) = new_N[                  card({i | i in new_V where i <= v})];
new_N: new_EV2N(new_V: v) = new_N[card(new_V)     + card({i | i in new_V where i <= v})];
new_N: new_C2N(new_C: c) =  new_N[card(new_V) * 2 + card({i | i in new_C where i <= c})];
%new_V: new_N2SV(new_N: n) = {v | v in new_V where new_SV2N(v) = n}[1];
%new_V: new_N2EV(new_N: n) = {v | v in new_V where new_EV2N(v) = n}[1];
new_V: new_N2V(new_N: n) = {v | v in new_V where new_SV2N(v) = n \/ new_EV2N(v) = n}[1];
new_C: new_N2C(new_N: n) = {c | c in new_C where  new_C2N(c) = n}[1];

N: solSV2N(agg_sol_V: v) = N[              card({ i | i in agg_sol_V where i <= v })];
N: solEV2N(agg_sol_V: v) = N[card(V)     + card({ i | i in agg_sol_V where i <= v })];
N: solC2N(agg_sol_C: c) =  N[card(V) * 2 + card({ i | i in agg_sol_C where i <= c })];
% aigg_sol_V: N2solSV(agg_sol_N: n) = {v | v in agg_sol_V where solSV2N(v) = n}[1];
% agg_sol_V: N2solEV(agg_sol_N: n) = {v | v in agg_sol_V where solEV2N(v) = n}[1];
% agg_sol_C: N2solC(agg_sol_N: n) =  {c | c in agg_sol_C where  solC2N(c) = n}[1];

N: newSV2N(new_V: v) = N[              card(agg_sol_V) + card({ i | i in new_V where i <= v })];
N: newEV2N(new_V: v) = N[card(V)     + card(agg_sol_V) + card({ i | i in new_V where i <= v })];
N: newC2N(new_C: c) =  N[card(V) * 2 + card(agg_sol_C) + card({ i | i in new_C where i <= c })];
% new_V: N2newSV(new_N: n) = {v | v in agg_sol_V where newSV2N(v) = n}[1];
% new_V: N2newEV(new_N: n) = {v | v in agg_sol_V where newEV2N(v) = n}[1];
% new_C: N2newC(new_N: n) =  {c | c in agg_sol_C where  newC2N(c) = n}[1];

N: SV2N(V: v) = N[              card({ i | i in V where i <= v })];
N: EV2N(V: v) = N[card(V)     + card({ i | i in V where i <= v })];
N: C2N(C: c) =  N[card(V) * 2 + card({ i | i in C where i <= c })];
%V: N2SV(N: n) = {v | v in V where SV2N(v) = n}[1];
%V: N2EV(N: n) = {v | v in V where EV2N(v) = n}[1];
V: N2V(N: n) = {v | v in V where SV2N(v) = n \/ EV2N(v) = n}[1];
C: N2C(N: n) = {c | c in C where  C2N(c) = n}[1];

array [N] of N: Nmap = [solSV2N(v)| v in agg_sol_V] ++ [newSV2N(v)| v in new_V]
                    ++ [solEV2N(v)| v in agg_sol_V] ++ [newEV2N(v)| v in new_V]
                    ++ [ solC2N(c)| c in agg_sol_C] ++ [ newC2N(c)| c in new_C];

% - Enum Map Checks - %
test is_sol(set of $$E: e, $$E: i) =
  if e = V
    then e[i] in {sol2N(n) | n in agg_sol_N}
  elseif e = C
    then e[i] in {sol2C(c) | c in agg_sol_C}
  elseif e = N
    then e[i] in {sol2V(v) | v in agg_sol_V}
    else assert(false, "unsupported is_sol call \(e) \(i), \(e[i])")
  endif;


% -------------------------- %
% --- DATA PARAMETERS ------ %
% -------------------------- %

% - Sol Data - %
array [sol_N] of int: sol_wait;
array [sol_N, sol_N] of int: sol_dist;
array [sol_N] of int: sol_x;
array [sol_N] of int: sol_y;

% - Data ----- %
array [new_N] of int: new_wait;
array [N] of int: wait = array1d(N, [if Nmap[n] in {sol2N(i) | i in agg_sol_N}
                                       then sol_wait[N2sol(Nmap[n])]
                                       else new_wait[N2new(Nmap[n])]
                                     endif | n in N] );

array [new_N] of int: new_x;
array [N] of int: x = array1d(N, [if Nmap[n] in {sol2N(i) | i in agg_sol_N}
                                    then sol_x[N2sol(Nmap[n])]
                                    else new_x[N2new(Nmap[n])]
                                  endif | n in N] );

array [new_N] of int: new_y;
array [N] of int: y = array1d(N, [if Nmap[n] in {sol2N(i) | i in agg_sol_N}
                                    then sol_y[N2sol(Nmap[n])]
                                    else new_y[N2new(Nmap[n])]
                                  endif | n in N] );

array [N, N] of int: dist = array2d(N, N, [ round(sqrt((x[n1] - x[n2])^2 + (y[n1] - y[n2])^2)) | n1,n2 in N]);

% -------------------------- %
% --- VARIABLES ------------ %
% -------------------------- %

% - Sol Variables - %
array [sol_N] of sol_V: sol_veh;
array [sol_N] of sol_N: sol_succ;
array [sol_N] of 0..infinity: sol_arr;

% - Variables - %
array [N] of var V: veh;
array [N] of var N: succ;
array [N] of var 0..infinity: arr;

% -------------------------- %
% --- REALIZATIONS --------- %
% -------------------------- %

% - Enum Realizations - %
bool: realized_V_(sol_V: v) = true;
bool: realized_C_(sol_C: c) = true;
bool: realized_N_(sol_N: n) = realized_wait_N(n)
                           /\ forall (m in sol_N) ( realized_dist_N(n, m) /\ realized_dist_N(m, n) )
                           /\ realized_veh_N(n)
                           /\ realized_succ_N(n)
                           /\ realized_arr_N(n);
                           
bool: realized_V(sol_V: v) = realized_V_(v)
                          /\ realized_N_(sol_SV2N(v))
                          /\ realized_N_(sol_EV2N(v));
bool: realized_C(sol_C: c) = realized_C_(c)
                          /\ realized_N_(sol_C2N(c));
bool: realized_N(sol_N: n) = realized_N_(n)
                          /\ if n in {sol_SV2N(v) | v in sol_V} union {sol_EV2N(v) | v in sol_V}
                               then realized_V_(sol_N2V(n))
                               else realized_C_(sol_N2C(n))
                             endif;                          

bool: realized(set of $$E: e, $$E: i) =
  if ENABLE_GARBAGE
    then if e[i] in sol_N
           then realized_N(sol_N[i])
         elseif e[i] in sol_C
           then realized_C(sol_C[i])
         elseif e[i] in sol_V
           then realized_V(sol_V[i])
           else assert(false, "Error, unsupported realization call: \(e[i]) of \(e)")
         endif
    else false
  endif;

% - Par Realizations -- %
bool: realized_wait_N(sol_N: n) = sol_arr[n] + sol_wait[n] <= now;
bool: realized_dist_N(sol_N: n1, sol_N: n2) = sol_arr[sol_succ[n1]] <= now \/ sol_arr[n2] <= now;

% - Var Realizations -- %
bool: realized_veh_N(sol_N: n) = sol_arr[n] <= now;
bool: realized_succ_N(sol_N: n) = sol_arr[sol_succ[n]] <= now;
bool: realized_arr_N(sol_N: n) = sol_arr[n] <= now;

% - Realization Sets -- %
set of sol_C: REALIZED_C = {c | c in sol_C where realized(sol_C, c)};
set of sol_V: REALIZED_V = {v | v in sol_V where realized(sol_V, v)};
set of sol_N: REALIZED_N = {n | n in sol_N where realized(sol_N, n)};

% -------------------------- %
% --- CONSTRAINTS ---------- %
% -------------------------- %

% % - Problem Constraints - %

% associate each vehicle with its
% start node and end node
constraint forall (v in V) 
  ( veh[SV2N(v)] = v /\    
    veh[EV2N(v)] = v );

% % new tours start at the deopot at time now
constraint forall (v in {new2V(i) | i in new_V})
  ( arr[SV2N(v)] = now);

% % EITHER FROM START DEPOT TO END DEPOT OR TO CUST
% constraint forall (v in V)
%   ( succ[SV2N(v)] in {C2N(c) | c in C} union {EV2N(v)} );

% same vehicle along subtour
constraint forall (n in {C2N(c) | c in C} union {SV2N(v) | v in V}, nextN in N where nextN = succ[n])
  ( veh[nextN] = veh[n] );
  
constraint forall (n in {SV2N(v) | v in V}
                   union {C2N(c) | c in C}) % travel time constraints
  ( arr[n] + wait[n] + dist[n,succ[n]] <= arr[succ[n]] );
  
constraint if length(succ) != 0
             then circuit(succ_w_agg)
             else true
           endif; % hamiltonian circuit


% A vehicle must serve at least one customer before leaving the depot
%constraint forall (v in V)
%  ( if succ[SV2N(v)] = EV2N(v)
%      then arr[EV2N(v)] >= 999999
%      else false
%    endif );

%constraint forall (v in 1..V)   % decide customers to serve first
 % ( arrival[next[C+v]] - dist[C+v, next[C+v]]
 %   >= max([requested[c] | c in 1..C where veh[c] = v]));

%constraint forall (c in 1..C)   % arrive before deadline
%  ( arr[c] <= deadline[c] );

% - Symmetry Breaking - %
constraint symmetry_breaking_constraint(
  forall (v in V diff {max(V)})
    ( succ[EV2N(v)] = SV2N(enum_next(V,v)) )
); % next of end node is following vehicles start node

constraint symmetry_breaking_constraint(
  if card(V) != 0
    then succ[EV2N(max(V))] = SV2N(min(V))
    else true
  endif
); % start node next of last end node is first

% test is_really_fixed(var int: x) = is_fixed(x) \/ card(dom(x))=1;

% test realized_succ(N: n) = 
%   is_really_fixed(succ_w_agg[n]);
% %   is_sol(N, n) /\ realized(sol_N, N2sol(n));

% test realized_pred(N: n) =
%   exists (pn in N)
%     (realized_succ(pn) /\ dom(succ_w_agg[pn])[1] = n);

% %   is_sol(N, n) /\ exists (pn in N)
% %                     (realized_succ(pn) /\ 
% %                                        (sol_succ[N2sol(pn)] = N2sol(n)
% %                                        \/ 
% %                                        (is_fixed(succ_w_agg[pn]) /\ fix(succ_w_agg[pn]) = n) 
% %                                        )
% %                                        );

% % test realized_pred(N: n) = 
% %   exists (pn in N)
% %     (realized_succ(pn) /\ sol2N(sol_succ[N2sol(pn)]) = n);

% opt N: fsucc(N: n) =
%   if is_sol(N, n)
%     then sol2N(sol_succ[N2sol(n)])
%     else absentN
%   endif;

% opt N: absentN = <>;

% array [int] of N: open_starts = [n | v in V, n = SV2N(v) where not(realized_pred(n))];
% % array [int] of N: open_ends = reverse([n | v in V, n = EV2N(v) where not(realized_succ(n))]);
% array [int] of N: open_ends_r =         [n | v in V, n = EV2N(v) where not(realized_succ(n))];
% % array [int] of N: open_ends = reverse(open_ends_r);
% array [int] of N: open_ends = if length(open_ends_r)=0 then [n | n in N where false] else reverse(open_ends_r) endif;

% % - Symmetry Breaking - %
% constraint symmetry_breaking_constraint(
%   let {array [int] of int: match = [i | i in index_set(open_starts) where N2V(open_starts[i]) = N2V(open_ends[i])];}
%   in if match = []
%     then forall (i in 1..length(open_starts)-1)
%            ( trace("i = \(i), open_ends[i] = \(open_ends[i]), dom(succ[open_ends[i]]) = \(dom(succ[open_ends[i]])), open_starts[i] = \(open_starts[i])\n", succ[open_ends[i]] = open_starts[i+1]) )
%     else forall (i in 2..length(open_starts) diff {match[1]})
%            ( succ[open_ends[i]] = open_starts[i] )
%       /\ succ[open_ends[1]] = open_starts[match[1]]
%       /\ succ[open_ends[match[1]]] = open_starts[1]
%   endif
% );

% - Online Constraints - %
% Lock customers when vehicle leaves depot
constraint forall ( v in V )
  ( if v in {sol2N(v) | v in agg_sol_N}
    %/\ has_sol(sol_SV2N, V2sol(v))
    /\ has_sol(sol_succ, sol_SV2N(V2sol(v)))
    /\ has_sol(sol_arr, sol_succ[sol_SV2N(V2sol(v))])
    /\ has_sol(sol_dist, sol_SV2N(V2sol(v)), sol_succ[sol_SV2N(V2sol(v))])
    /\ now >= sol_arr[sol_succ[sol_SV2N(V2sol(v))]] - sol_dist[sol_SV2N(V2sol(v)),sol_succ[sol_SV2N(V2sol(v))]]
      then forall ( n in N )
        ( if n in {sol2N(n) | n in agg_sol_N}
          /\ has_sol(sol_veh, N2sol(n))
            then veh[n] = v <-> sol_veh[N2sol(n)] = V2sol(v)
          endif )
    endif );

% lock succ[i] when leaving i
constraint forall ( n in N )
  ( if n in {sol2N(n) | n in agg_sol_N}
    /\ has_sol(sol_succ, N2sol(n)) 
    /\ has_sol(sol_arr, N2sol(n))
    /\ has_sol(sol_wait, N2sol(n))
    /\ now >= sol_arr[N2sol(n)] + sol_wait[N2sol(n)]
    /\ sol_succ[N2sol(n)] in agg_sol_N
    /\ not(n in {EV2N(v) | v in V}) % MAKES SURE WE DO NOT COMMIT SYMMETRY BREAKING
      then succ[n] = sol2N(sol_succ[N2sol(n)])
    endif );

% Commit arr when arrived
constraint forall ( n in N )
  ( if n in {sol2N(n) | n in agg_sol_N}
    /\ has_sol(sol_arr, N2sol(n))
    /\ now >= sol_arr[N2sol(n)]
      then arr[n] = sol_arr[N2sol(n)]
      else arr[n] >= now
    endif );

% -------------------------- %
% --- OBJECTIVE ------------ %
% -------------------------- %

var int: cost;
constraint cost = agg_cost + sum (v in V) ( arr[EV2N(v)] - ( arr[succ[SV2N(v)]] - dist[SV2N(v),succ[SV2N(v)]] ) );
solve :: int_search(succ_w_agg, dom_w_deg, indomain_min) minimize cost;

% -------------------------- %
% --- AGGREGATION ---------- %
% -------------------------- %

% - Sum Aggregation: Cost - %
int: agg_cost = sol_agg_cost + sum (v in sol_V diff agg_sol_V) (sol_arr[sol_EV2N(v)] - ( sol_arr[sol_succ[sol_SV2N(v)]] - sol_dist[sol_SV2N(v),sol_succ[sol_SV2N(v)]] ));
int: sol_agg_cost;

% - Circuit Aggregation: Succ - %

array [sol_N] of 0..card(sol_N): sol_agg_succ; % given
array [int] of 0..card(sol_N): new_agg_succ_ = agg_circuit(sol_agg_succ, sol_succ); % = agg_circuit
array [N] of 0..card(N): new_agg_succ = array1d(N, [ if is_sol(N, n) /\ new_agg_succ_[N2sol(n)] != 0
                                                       then sol2N(sol_N[new_agg_succ_[N2sol(n)]])
                                                       else 0
                                                     endif | n in N]);

% combine: replace old jumps with new, otherwise use old jumps
array [N] of 0..card(N): agg_succ = array1d(N, [ if new_agg_succ[n] != 0
                                              then new_agg_succ[n]
                                            elseif is_sol(N, n) /\ sol_agg_succ[N2sol(n)] != 0
                                              then sol2N(sol_N[sol_agg_succ[N2sol(n)]])
                                              else 0
                                            endif | n in N]);
                                           
% succ array with jumps included
array [N] of var N: succ_w_agg = array1d(N, [ if is_sol(N, n) 
                                                       then N[next(agg_succ, succ, n)]
                                                       else succ[n]
                                                     endif | n in N]);

array [int] of int: agg_circuit(array [int] of int: sol_agg, array [int] of int: succ) =
  % if no garbage, do nothing
  if length([i | i in index_set(succ) where garbage(index_set(succ), next(sol_agg, succ, i))]) = 0
    then [0 | i in index_set(succ)]
  % if all is garbage, what to do? TODO?
  elseif forall (i in index_set(succ)) (garbage(index_set(succ), next(sol_agg, succ, i)))
    then []
  % else (not all but some garbage), find jumps
    else let {int: fng = first_nongarbage(sol_agg, succ, index_set(succ)[1]);
              array [int] of int: jumps_ = agg_circuit_(sol_agg, succ, fng, fng);
              array [int,1..2] of int: jumps = array2d(1..length(jumps_) div 2 + card(sol_N), 1..2, jumps_ ++ [ if i = 1 then n else 0 endif | n in sol_N, i in 1..2])}
         in array1d(sol_N, [jump_from(jumps, n) | n in sol_N])
  endif;

int: jump_from(array [int, 1..2] of int: jumps, int: from) =
    jumps[min (i in index_set_1of2(jumps) where jumps[i,1] = from) (i), 2];

% Locate jumps
array [int] of int: agg_circuit_(array [int] of int: sol_agg, array [int] of int: succ, int: n, int: start) =
  if next(sol_agg, succ, n) == start
    then []
  elseif garbage(sol_N, next(sol_agg, succ, n))
    then let {int: jump_dest = agg_circuit__(sol_agg, succ, n);
              array [int] of int: jump = [n, jump_dest]}
         in if jump_dest = n
              then []
            elseif jump_dest = start
              then [n, jump_dest]
              else [n, jump_dest] ++ agg_circuit_(sol_agg, succ, jump_dest, start)
            endif
    else agg_circuit_(sol_agg, succ, next(sol_agg, succ, n), start)
  endif;

% End destination of a given jump
int: agg_circuit__(array [int] of int: sol_agg, array [int] of int: succ, int: n) =
  if garbage(sol_N, next(sol_agg, succ, n))
    then agg_circuit__(sol_agg, succ, next(sol_agg, succ, n))
    else next(sol_agg, succ, n)
  endif;

int: first_nongarbage(array [int] of int: sol_agg, array [int] of int: asucc, int: e) =
  if garbage(index_set(asucc), e) /\ not_a_jump(sol_agg, e)
    then first_nongarbage(sol_agg, asucc, next(sol_agg, asucc, e))
    else e
  endif;

% successor w.r.t sol jumps
int: next(array [int] of int: sol_agg, array [int] of int: succ, int: n) =
  if sol_agg[n] != 0
    then sol_agg[n]
    else succ[n]
  endif;
var int: next(array [int] of int: sol_agg, array [int] of var int: succ, int: n) =
  if sol_agg[n] != 0
    then sol_agg[n]
    else succ[n]
  endif;

bool: not_a_jump(array [int] of int: sol_agg, int: n) = sol_agg[n] != 0;


% -------------------------- %
% --- GARBAGE NOMINATION --- %
% -------------------------- %

% - Forall Nomination 1D - %
set of $$E: agg_idx_forall(set of $$E: e) =
  {i | i in index_set(e) where not(realized(e, i))};
  
% - Forall Nomination 2D - %
set of $$E: agg_idx_forall_1of2(array [$$E, $$F] of bool: realized) = 
  {i | i in index_set_1of2(realized) where exists(j in index_set_2of2(realized))(not(realized[i,j]))};
set of $$F: agg_idx_forall_2of2(array [$$E, $$F] of bool: realized) = 
  {j | j in index_set_2of2(realized) where exists(i in index_set_1of2(realized))(not(realized[i,j]))};

array [sol_C, sol_N] of bool: agg_idx_forall_001 =
 array2d(sol_C, sol_N,
 [if nextN = sol_succ[sol_C2N(c)]
    then realized(sol_C, c) /\ realized(sol_N, nextN) 
    else true
  endif | c in sol_C, nextN in sol_N]);
  
array [sol_N, sol_N] of bool: agg_idx_forall_002 =
 array2d(sol_N, sol_N,
 [if nextN = sol_succ[n]
    then realized(sol_N, n) /\ realized(sol_N, nextN) 
    else true
  endif | n in sol_N, nextN in sol_N]);

% - Sum Nomination 1D - %
set of $$E: agg_idx_sum(set of $$E: e) =
  {i | i in index_set(e) where not(realized(e, i))};

% - Circuit Nomination - %
set of $$E: agg_idx_circuit(array [int] of int: sol_agg, array [$$E] of $$E: asucc) =
    if length([i | i in index_set(asucc) where realized(index_set(asucc), next(sol_agg, asucc, i))]) = length(index_set(asucc))
    /\ {i | i in index_set(asucc) where realized(index_set(asucc), next(sol_agg, asucc, i))} = index_set(asucc)
      then {}
      else {i | i in agg_idx_circuit_(sol_agg, asucc, agg_idx_circuit__(sol_agg, asucc, index_set(asucc)[1]),
                                                      agg_idx_circuit__(sol_agg, asucc, index_set(asucc)[1]), false)}
    endif;

array [int] of $$E: agg_idx_circuit_(array [int] of int: sol_agg, array [$$E] of $$E: asucc, $$E: n, $$E: start, bool: started) =
  if next(sol_agg, asucc, n) == start
    then [next(sol_agg, asucc, n)]
  elseif realized(sol_N, next(sol_agg, asucc, n)) /\ started
    then agg_idx_circuit_(sol_agg, asucc, next(sol_agg, asucc, n), start, started)
  elseif realized(sol_N, next(sol_agg, asucc, n))
    then [next(sol_agg, asucc, n)] ++ agg_idx_circuit_(sol_agg, asucc, next(sol_agg, asucc, n), start, true)
    else [next(sol_agg, asucc, n)] ++ agg_idx_circuit_(sol_agg, asucc, next(sol_agg, asucc, n), start, false)
  endif;

$$E: agg_idx_circuit__(array [int] of int: sol_agg, array [$$E] of $$E: asucc, $$E: e) =
  if realized(sol_N, e) /\ not_a_jump(sol_agg, e)
    then agg_idx_circuit__(sol_agg, asucc, next(sol_agg, asucc, e))
    else e
  endif;

% -------------------------- %
% --- GARBAGE OMISSION ----- %
% -------------------------- %

set of sol_V: agg_sol_V_imd = agg_idx_forall(sol_V);
set of sol_C: agg_sol_C_imd = agg_idx_forall_1of2(agg_idx_forall_001)
                        union agg_idx_forall(sol_C);
set of sol_N: agg_sol_N_imd = agg_idx_forall_2of2(agg_idx_forall_001)
                        union agg_idx_forall_1of2(agg_idx_forall_002)
                        union agg_idx_forall_2of2(agg_idx_forall_002)
                        union agg_idx_circuit(sol_agg_succ, sol_succ) % put in the jumps sol_agg_succ_1d
                        union {sol_SV2N(i) | i in agg_sol_V_imd}
                        union {sol_EV2N(i) | i in agg_sol_V_imd}
                        union {sol_C2N(i) | i in agg_sol_C_imd};
set of sol_V: agg_sol_V = { i | i in sol_V where sol_SV2N(i) in agg_sol_N_imd }
                    union { i | i in sol_V where sol_EV2N(i) in agg_sol_N_imd };
set of sol_C: agg_sol_C = { i | i in sol_C where sol_C2N(i) in agg_sol_N_imd };
set of sol_N: agg_sol_N = {sol_SV2N(i) | i in agg_sol_V}
                    union {sol_EV2N(i) | i in agg_sol_V}
                    union {sol_C2N(i) | i in agg_sol_C};
                                                                                                   
bool: garbage(set of $$E: e, $$E: i) =
  if e[i] in sol_N
    then not(sol_N[i] in agg_sol_N)
  elseif e[i] in sol_C
    then not(sol_C[i] in agg_sol_C)
    else not(sol_V[i] in agg_sol_V)
  endif;
  
set of sol_V: GARBAGE_V = {v | v in sol_V where garbage(sol_V, v)};
% set of sol_V: GARBAGE_V = {v | v in { i | i in sol_V where sol_SV2N(i) in agg_sol_N_imd } union { i | i in sol_V where sol_EV2N(i) in agg_sol_N_imd }};
% set of V: ReAdd_V = {v | v in V where fix(arr[EV2N(v)]) <= now + incr};

% --- PROJECTIONS ---------- %

% --- STATIC DATA ---------- %

% --- OUTPUT --------------- %

%array [int] of var string: veh_map = [if v in {sol2V[i] | i in index_set(sol2V)} then show(inverse(sol2V)(v)) else show(inverse(new2V)(v)) endif | v in veh];

% output [""
%      ++ "\nnow = \(now+10);"
%      ++ "\nsol_N = \(N);"
%      ++ "\nsol_V = \(V);"
%      ++ "\nsol_C = \(C);"
%      ++ "\nsol_dist = array2d(sol_N, sol_N, \(dist) );"
%      ++ "\nsol_wait = \(wait);"
%      ++ "\nsol_succ = \(succ);"
%      ++ "\nsol_veh = \(veh);"
%      ++ "\nsol_arr = \(arr);"
%      ++ "\nsol_agg = \(agg);"
% %      ++ "--END-SOL-OUTPUT--"
%     ++ "\nnew_V = {v2};"
%     ++ "\nnew_C = {c2};"
%     ++ "\nnew_wait = [0,0,13];"
%     ++ "\nnew_dist_from = array2d(new_N, sol_N, [ if nn in {i | i in new_SV2N} union {i | i in new_EV2N} /\\ sn in {i | i in sol_SV2N} union {i | i in sol_EV2N} then 0 else 20 endif | nn in new_N, sn in sol_N] );"                                   
%     ++ "\nnew_dist_to = array2d(sol_N, new_N, [ if nn in {i | i in new_SV2N} union {i | i in new_EV2N} /\\ sn in {i | i in sol_SV2N} union {i | i in sol_EV2N} then 0 else 20 endif | sn in sol_N, nn in new_N] );"                               
%     ++ "\nnew_dist_between = array2d(new_N, new_N, [0, 0,20, 0, 0,20,20,20, 0]);"
%     ++ "\n"
%     ++ "\n"
%     ++ "\nRlz_C = \(REALIZED_C)"
%     ++ "\nRlz_V = \(REALIZED_V)"
%     ++ "\nRlz_N = \(REALIZED_N)"
% %     ++ "\nagg_sol_C_imd = \(agg_sol_C_imd)"
% %     ++ "\nagg_sol_V_imd = \(agg_sol_V_imd)"
%     ++ "\nagg_sol_N = \(agg_sol_N)"
%     ++ "\nagg_sol_C = \(agg_sol_C)"
%     ++ "\nagg_sol_V = \(agg_sol_V)"
% %     ++ "\nagg_sol_N = \(agg_idx_forall_2of2(agg_idx_forall_001))"
% %     ++ "\n\t\t UNION \(agg_idx_forall_1of2(agg_idx_forall_002))"
% %     ++ "\n\t\t UNION \(agg_idx_forall_2of2(agg_idx_forall_002))"
% %     ++ "\n\t\t UNION \(agg_idx_circuit(sol_succ))"
% %     ++ "\n\t\t UNION \({sol_SV2N[i] | i in agg_sol_V_imd})"
% %     ++ "\n\t\t UNION \({sol_EV2N[i] | i in agg_sol_V_imd})"
% %     ++ "\n\t\t UNION \({sol_C2N[i] | i in agg_sol_C_imd})"
% %     ++ "\n"
%     ++ "\nnV = \(card(V))"
%     ++ "\nnC = \(card(C))"
%     ++ "\nnN = \(card(N))"
%      ++ "\n"
%      ++ "\nobj = \(cost);"
%  ];

string: absent_print (array [int] of opt N: arr, int: i) =
  if i = length(arr)
    then ""
  elseif absent(arr[i])
    then "absent_N," ++ absent_print(arr, i+1)
    else show(arr[i]) ++ absent_print(arr, i+1)
  endif;


 output ["--START-SOL-OUTPUT--"
     ++ "\nnow = \(now+incr);"
     ++ "\nsol_N = \(N);"
     ++ "\nsol_V = \(V);"
     ++ "\nsol_C = \(C);"
     ++ "\nsol_dist = array2d(sol_N, sol_N, \(dist) );"
     ++ "\nsol_x = array1d(sol_N, \(x) );"
     ++ "\nsol_y = array1d(sol_N, \(y) );"
     ++ "\nsol_wait = \(wait);"
     ++ "\nsol_succ = \(succ);"
     ++ "\nsol_veh = \(veh);"
     ++ "\nsol_arr = \(arr);"
     ++ "\nsol_agg_cost = \(agg_cost);"
%      ++ "\nsol_agg_succ = ["++join(",", [ if occurs(n) then show(n) else "absent_N" endif | n in sol_agg_succ])++"];"
     ++ "\nsol_agg_succ = \(agg_succ);"
     ++ "--END-SOL-OUTPUT--"
     ++ "\n"
     ++ "--START-OBJ-OUTPUT--\(cost)--END-OBJ-OUTPUT--"
     ++ "--START-PRV-OUTPUT--\(card(sol_V) - card(agg_sol_V))--END-PRV-OUTPUT--"
     ++ "--START-PRC-OUTPUT--\(card(sol_C) - card(agg_sol_C))--END-PRC-OUTPUT--"
     ++ "--START-VRL-OUTPUT--\(card({v | v in V where fix(arr[EV2N(v)]) <= now + incr}))--END-VRL-OUTPUT--"

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
