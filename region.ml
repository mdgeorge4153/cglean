module Make (F : Numbers.OrderedField) = struct

module FU = Numbers.OrderedFieldUtils (F)
open F
open FU

(******************************************************************************)
(** 2-vectors *****************************************************************)
(******************************************************************************)

type point  = number * number

(* some helpers for working with 2-vectors *)
let dot   (x1,y1) (x2,y2) = x1*x2 + y1*y2
let smult s (x,y) = s*x, s*y

let ( +! ) (x1,y1) (x2,y2) = x1 + x2, y1 + y2
let ( -! ) p1 (x,y)        = p1 +! (-x,-y)
let ( *! ) (x1,y1) (x2,y2) = x1*y2 - x2*y1
let ( *. ) v1 v2           = dot v1 v2

(******************************************************************************)
(** Point comparisons *********************************************************)
(******************************************************************************)

type comparison_result = Lt | Eq | Gt
let  int_cmp f x y = match f x y with | Lt -> -1 | Gt -> 1 | Eq -> 0
let  sign x = if not (is_non_neg x) then Lt else if x === zero then Eq else Gt

(* sorts two points lexicographically (by x and then by y) *)
let compare_points (x1, y1) (x2, y2) = match sign (x1 - x2) with
    | Lt -> Lt
    | Gt -> Gt
    | Eq -> sign (y1 - y2)

module PointCompare = struct
  type t = point
  let compare = int_cmp compare_points
end

module PointMap = Map.Make(PointCompare)

(******************************************************************************)
(** Region type ***************************************************************)
(******************************************************************************)

(* A region is stored as a map; each vertex in the boundary of the region has a
 * corresponding key.  The values are lists of edges.  We refer to the source
 * of an edge as the key under which the edge is stored.
 *
 * a region r is valid if
 *  1. the target of every edge is less than the source (in the compare_points order)
 *  2. the target of every edge has a corresponding vertex in the map
 *  3. the edges at each source are sorted (by the compare_edges_around order)
 *  4. the edges and vertices are all interior-disjoint
 *)
type edge   = {
  target   : point;
  left_in  : bool;
  right_in : bool;
}
type region = edge list PointMap.t

let vertices r = List.map fst (PointMap.bindings r)

let edges r =
  let rec helper r = match r with
    | []          -> []
    | (p, es)::tl -> (List.map (fun e -> p,e.target) es) @ helper tl
  in helper (PointMap.bindings r)

(******************************************************************************)
(** More comparisons **********************************************************)
(******************************************************************************)

(* determines whether the edge from p to p1 lies above or below the edge from p
 * to p2
 *
 * assumes that p1 and p2 are less than p in the compare_points ordering
 *)
let compare_slopes_from p p1 p2 = sign ((p2 -! p) *! (p1 -! p))
let cmp_edges p e1 e2 = int_cmp (compare_slopes_from p) e1.target e2.target


(* compares (point, edge list) pairs by the point *)
let compare_vertex (p1, es1) (p2, es2) = Pervasives.(~-) (int_cmp compare_points p1 p2)


(******************************************************************************)
(** Creation ******************************************************************)
(******************************************************************************)

(* given a list [a; b; c; d], return [(a,b); (b,c); (c,d); (d,a)] *)
let adjacent_pairs l =
  let rec helper l' last = match l' with
    | x1 :: x2 :: xs  -> (x1, x2)  :: helper (x2 :: xs) last
    | x  :: []        -> [(x, last)]
    | []              -> failwith "this should never happen"
  in match l with
    | []      -> []
    | x :: xs -> helper l x


(* return the binding of p in m, or None if none exists *)
let get p m = if PointMap.mem p m then Some (PointMap.find p m) else None

(* add the point if it didn't already exist, with an empty list *)
let insert p m = if PointMap.mem p m then m else PointMap.add p [] m 

(* append the given edge to the point in the map *)
let append p e m = match get p m with
  | Some es -> PointMap.add p (List.merge (cmp_edges p) es [e]) m
  | None    -> PointMap.add p [e] m


let create points =
  (* we simply loop through all the edges, adding each to the map *)
  let edges = adjacent_pairs points in
  let rec add_edges l m = match l with
    | []        -> m
    | (x,y)::es ->
        let swap   = match compare_points x y with
                      | Lt -> false | Gt -> true
                      | Eq -> failwith "invalid input" in
        let source = if swap then x else y in
        let target = if swap then y else x in
        let edge   = {target=target; left_in = swap; right_in = not swap} in 
        add_edges es (append source edge (insert target m))
  in add_edges edges PointMap.empty

(******************************************************************************)
(** Point location ************************************************************)
(******************************************************************************)

type containment = Inside   | Outside   | Boundary
type crossing    = OddCross | EvenCross | InsideCross

let add c1 c2 = match c1, c2 with
  | InsideCross, _
  | _, InsideCross -> InsideCross
  | _ when c1 = c2 -> EvenCross
  | _              -> OddCross

let locate p (r:region) =
  (* determines whether a ray cast down from p intersects t <-- s an even or odd
   * number of times.  Returns InsideCross if p lies on  t <-- s.
   *)
  let crosses_edge p s e =
    let t = e.target in
    let (px,py), (sx,sy), (tx,ty) = p, s, t in
    match sign (px - sx), sign (px - tx) with
      | Lt, Lt -> EvenCross
      | Gt, Gt -> EvenCross
      | Gt, Lt -> failwith "s < p < t but t < s"
      | Eq, Eq when ty <= py && py <= sy -> InsideCross
      | Lt, Eq -> EvenCross (* this prevents double-counting when two edges
                               share a common endpoint that lies south of the
                               test point *)
      | Eq, Eq -> EvenCross
      | _ -> (* tx <= p <= sx and tx < sx *)
             (* there could be an intersection; find y intercept and compare *)
             match sign ((p -! s) *! (t -! s)) with
               | Eq -> InsideCross
               | Gt when Pervasives.(<>) e.left_in e.right_in
                    -> OddCross
               | _  -> EvenCross
  in

  (* determines how to count p crossing v *)
  let crosses_vert p v = if fst p === fst v && snd p === snd v
                         then InsideCross
                         else EvenCross
  in

  let rec edge_crossings (l : (point * edge list) list) acc = match l with
    | []         -> acc
    | (s,es)::tl -> edge_crossings tl (List.fold_left add acc (List.map (crosses_edge p s) es))
  in
  let edge_crossings = edge_crossings (PointMap.bindings r) EvenCross in

  let vert_crossings = List.map (crosses_vert p) (vertices r) in
  let vert_crossings = List.fold_left add EvenCross vert_crossings in
  match add edge_crossings vert_crossings with
    | InsideCross -> Boundary
    | EvenCross   -> Outside
    | OddCross    -> Inside


let contains p r = match locate p r with | Inside -> true | _ -> false

(* return the closest point to p on the line segment (x,y) *)
let closest_point_on p (x,y) =
  let xy = y -! x in
  let xp = p -! x in
  let d  = (xy *. xp) / (xy *. xy) in
  if zero >= d then x
  else if d >= one then y
  else x +! smult d xy

let find_closest (r : region) p =
  if not (contains p r) then p
  else
    (* the closest point on each edge: *)
    let closest   = List.map (closest_point_on p) (edges r) in

    (* Adds all isolated points by themselves as well *)
    let closest   = List.rev_append closest (vertices r) in

    (* the distance squared from p to p' *)
    let dp p'     = let diff = p -! p' in diff *. diff in

    (* returns whichever of p1, p2 is closer to p *)
    let min p1 p2 = if (dp p1) < (dp p2) then p1 else p2 in

    (* since p is contained in r, r must have an edge *)
    List.fold_left min (List.hd closest) closest

(******************************************************************************)
(** Union *********************************************************************)
(******************************************************************************)

(* returns indices i and j such that
 *  - for every k in [0,i), f a.(k) = Gt
 *  - for every k in [i,j), f a.(k) = Eq
 *  - for every k in [j,n), f a.(k) = Lt
 *)
let binary_search f a =
  let open Pervasives in
  (* returns i in [m,n) such that
   *  - for every k in [m, i), f a.(k) = Lt
   *  - for every k in [i, n), f a.(k) <> Lt
   *)
  let rec lower_helper m n =
    if m >= n then m else
    let mid = (m + n) / 2 in
    match f a.(mid) with
      | Gt -> lower_helper (mid+1) n
      | _  -> lower_helper m mid
  in

  (* returns j *)
  let rec upper_helper m n =
    if m >= n then m else
    let mid = (m + n) / 2 in
    match f a.(mid) with
      | Lt -> upper_helper m mid
      | _  -> upper_helper (mid+1) n
  in

  let n = Array.length a in
  lower_helper 0 n, upper_helper 0 n


(* should return Gt if the edge from source to target lies above pt *)
let compare_edge_to_point pt (source, {target=target}) =
  compare_slopes_from source pt target


(* List.mapi doesn't exist in OCaml 3.12 *)
let mapi f l =
  let rec helper i l = match l with
    | [] -> []
    | x::xs -> (f i x)::helper (succ i) xs
  in
  helper 0 l

(* given edges starting at p1 and q1 and ending in p2.target and q2.target,
 * return an (x, es) pair where p1->p2 and q1->q2 intersect at x and
 * es are the ``rest'' of p1->p2 and q1->q2, or None if no such intersection
 * exists.
 *
 * fails if p1 lies on q1->q2 or vice versa
 *)
let segment_intersect (p1, p2) (q1, q2) =
  (* we solve the equation p1 + s(p2 - p1) = q1 + t(q2 - q1) *)
  let dq  = q2.target -! q1 in
  let dp  = p2.target -! p1 in
  let d1  = p1 -! q1 in
  let det = dq *! dp in
  if det === zero then None (* lines are parallel - no ix *)
  else
    let s = d1 *! dp / det in
    let t = d1 *! dq / det in
    let x = p1 +! smult t dp in
    (* if 0 <= s <= 1 and 0 <= t <= 1 then there is an intersection *)
    match sign s, sign (one - s), sign t, sign (one - t) with
      | Lt, _,  _,  _
      | _,  Lt, _,  _
      | _,  _,  Lt, _
      | _,  _,  _,  Lt -> None
      | Eq, _,  _,  _  -> failwith "p1 lies on q1->q2"
      | _,  _,  Eq, _  -> failwith "q1 lies on p1->p2"
      | _,  Gt, _,  Gt -> Some (x, [q2; p2])
      | _,  Eq, _,  Gt -> Some (x, [p2]) (* q2 ends at x *)
      | _,  Gt, _,  Eq -> Some (x, [q2]) (* p2 ends at x *)
      | _,  Eq, _,  Eq -> Some (x, [])   (* both lines end at x *)

(* merge_edges_from  p es1 es2 merges two lists of edges leaving p.  In
 * addition to the merged output, it produces two lists of "extra" edges
 * that are created when two input edges overlap:
 *
 *  q1 <---- q2 <----- p
 *
 * produces an edge to q2 and an "extra" edge (q2, q1)
 *
 * the new points in the extras lists are guaranteed to be in the interior of
 * edges from the corresponding input edge lists
 *)
let rec merge_edges_from (p : point) (es1 : edge list) (es2 : edge list)
                       : (point * edge list) list
                       * (point * edge list) list
                       * edge list
                       =
  let open Pervasives in
  match es1, es2 with
  | [],  []  -> [], [], []
  | [],  es2 -> [], [], es2
  | es1, []  -> [], [], es1
  | e1::es1, e2::es2 -> match compare_slopes_from p e1.target e2.target with
    | Lt -> let extras1, extras2, result = merge_edges_from p es1 (e2::es2)
            in  extras1, extras2, e1::result
    | Gt -> let extras1, extras2, result = merge_edges_from p (e1::es1) es2
            in  extras1, extras2, e2::result
    | Eq -> (* here the two edges overlap, so we need to create an extra edge
               from the end of the shorter one to the end of the longer one.*)
            let extras1, extras2, result = merge_edges_from p es1 es2 in
            let edge = {target   = (zero,zero);
                        left_in  = e1.left_in  || e2.left_in;
                        right_in = e1.right_in || e2.right_in
                       }
            in
            match compare_points e1.target e2.target with
              | Lt -> (e2.target, [e1])::extras1, extras2,
                      {edge with target = e2.target}::result
              | Gt -> extras1, (e1.target, [e2])::extras2,
                      {edge with target = e1.target}::result
              | Eq -> extras1, extras2,
                      {edge with target = e1.target}::result

(* merge_points ps1 ps2 produces a new list containing the vertices and edges
 * of both ps1 and ps2.  It does not detect intersections between the edges,
 * but it does merge line segments that overlap.
 *
 * ps1 and ps2 are assumed ordered largest to smallest; the return
 * value is also ordered this way.
 *)
let rec merge_points ps1 ps2 =
  let open Pervasives in
  match ps1, ps2 with
  | [],  []  -> []
  | ps1, []  -> ps1
  | [],  ps2 -> ps2
  | (p1, es1)::tl1, (p2, es2)::tl2 -> match compare_points p1 p2 with
    | Gt -> (p1,es1)::merge_points tl1 ps2
    | Lt -> (p2,es2)::merge_points ps1 tl2
    | Eq -> let extras1, extras2, es = merge_edges_from p1 es1 es2 in
            let tl1 = List.merge compare_vertex tl1
                                 (List.sort compare_vertex extras1) in
            let tl2 = List.merge compare_vertex tl2
                                 (List.sort compare_vertex extras2) in
            (p1, es)::merge_points tl1 tl2

(* merge takes two arguments:
 *   - worklist has the form of PointMap.bindings r for a region r, but it is
 *     ordered from largest to smallest
 *   - status is an array of disjoint edges, sorted from top to bottom
 * merge returns a pair (result, ends):
 *   - result is a valid region
 *   - ends is an array of endpoints, one for each line in status
 *)
let rec merge (worklist : (point * edge list) list) 
              (status   : (point * edge)      array)
              : (point * edge list) list
              * point array
              =
  let open Pervasives in
  match worklist with
  | [] -> begin
            assert (Array.length status = 0);
            [], Array.make 0 (zero, zero)
          end
  | (pt, old_es)::tl ->

      (* split status into
       *  - edges above pt (indices k in [0, i))
       *  - edges below pt (indices k in [j, n))
       *      these will go into the status structure for the recursive call
       *  - edges passing through pt (indices k in [i, j))
       *      these will be consumed and replaced with a different set of new edges
       *      for the recursive call.
       *)
      let n   = Array.length status in
      let i,j = binary_search (compare_edge_to_point pt) status in

      let above = Array.sub status 0 i in
      let equal = Array.sub status i (j - i) in
      let below = Array.sub status j (n - j) in

      (* we need to find the new edges that come out of this point *)
      let new_es = List.filter (fun e -> compare_points e.target pt = Lt)
                               (List.map snd (Array.to_list equal)) in
      let new_es = List.rev new_es in
      (* and integrate them *)

      let extras1, extras2, es = merge_edges_from pt old_es new_es in

      let worklist = merge_points tl extras1 in
      let worklist = merge_points worklist extras2 in

      let outgoing = Array.of_list (List.map (fun e -> (pt, e)) es) in

      (* find potential new intersections:
       *  - if there's any above and any new, then the top new can intersect the
       *    bottom above
       *
       *  - if there's any below and any new, then the bot new can intersect the
       *    top above
       *
       *  - if there's no new, then the bottom top may intersect the top bottom
       *)

      let add_intersection a1 a2 worklist =
        if Array.length a1 = 0 || Array.length a2 = 0 then
          worklist
        else
          let e1 = a1.(Array.length a1 - 1) in
          let e2 = a2.(0) in
          match segment_intersect e1 e2 with
            | None    -> worklist
            | Some ix -> merge_points worklist [ix]
      in

      let worklist = add_intersection above outgoing worklist in
      let worklist = add_intersection outgoing below worklist in
      let worklist = if Array.length outgoing = 0
                     then add_intersection above below worklist
                     else worklist in

      (* make recursive call *)
      let newstatus = Array.concat [above; outgoing; below] in
      let child, endpoints = merge worklist newstatus in

      (* construct return value *)
      let edges = mapi (fun k e -> {e with target = endpoints.(i + k)}) es in
      let arrR  = (pt, edges)::child in

      (* insert our new arrangement into the return structure *)
      let n     = Array.length endpoints in
      let above = Array.sub endpoints 0 i in
      let equal = Array.make (j - i) pt in

      let nout  = Array.length outgoing in
      let below = Array.sub endpoints (i + nout) (n - i - nout) in

      (arrR, Array.concat [above; equal; below])

let edge_in p q r =
  let half = inv (one + one) in
  let mid = smult half (p +! q) in
  locate mid r = Inside

(* removes all of the vertices and edges of result that are in r1 or r2 *)
let rec prune result r1 r2 = match result with
  | []          -> []
  | (p, es)::tl -> if locate p r1 = Inside || locate p r2 = Inside
                   then prune tl r1 r2
                   else (
                     p,
                     List.filter (fun {target = q} -> not (edge_in p q r1
                                                        || edge_in p q r2)) es
                   ) :: prune tl r1 r2

let region_of_list l = List.fold_left (fun m (k,v) -> PointMap.add k v m) PointMap.empty l

let union r1 r2 =
  let initial_worklist = merge_points (List.rev (PointMap.bindings r1))
                                      (List.rev (PointMap.bindings r2)) in

  let initial_status = Array.make 0 ((zero,zero), {target=(zero,zero); left_in = false; right_in = false}) in
  let result, _ = merge initial_worklist initial_status in
  let result = prune result r1 r2 in
  let result = region_of_list result in

  result
end



(*
** vim: ts=2 sw=2 et ai
*)
