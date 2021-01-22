module Env = Map.Make(String)

module IntSet = Set.Make(struct type t = int let compare = compare end)
module IntMap = Map.Make(struct type t = int let compare = compare end)

module Make (Meta : sig type t end) = struct
  module Node = Node.Make(Meta)
  open Node

  let pp f x =
    let seen = ref Id.Set.empty in
    let rec aux f t =
      let Term t = t in
      if Id.Set.mem t.id !seen then
        Fmt.string f "..."
      else (
        seen := Id.Set.add t.id !seen;
        match t.ty with
        | Constant None ->
          begin match t.bind with
            | Some ctx -> aux f ctx
            | None ->
              match Current_incr.observe t.v with
              | Error (_, `Active _) -> Fmt.string f "(input)"
              | _ -> Fmt.string f "(const)"
          end
        | Constant (Some l) -> Fmt.string f l
        | Map_input { source = _; info = Ok label } -> Fmt.string f label
        | Map_input { source = _; info = Error `Blocked } -> Fmt.string f "(blocked)"
        | Map_input { source = _; info = Error `Empty_list } -> Fmt.string f "(empty list)"
        | Opt_input { source } -> Fmt.pf f "[%a]" aux source
        | Bind_in (x, name) -> Fmt.pf f "%a@;>>=@;%s" aux x name
        | Bind_out x -> aux f (Current_incr.observe x)
        | Primitive {x; info; meta = _ } -> Fmt.pf f "%a@;>>=@;%s" aux x info
        | Pair (x, y) -> Fmt.pf f "@[<v>@[%a@]@,||@,@[%a@]@]" aux x aux y
        | Gate_on { ctrl; value } -> Fmt.pf f "%a@;>>@;gate (@[%a@])" aux value aux ctrl
        | List_map { items; output } -> Fmt.pf f "%a@;>>@;list_map (@[%a@])" aux items aux (Current_incr.observe output)
        | Option_map { item; output } -> Fmt.pf f "%a@;>>@;option_map (@[%a@])" aux item aux (Current_incr.observe output)
        | State x -> Fmt.pf f "state(@[%a@])" aux x.source
        | Catch x -> Fmt.pf f "catch(@[%a@])" aux x.source
        | Map x -> aux f x
        | Collapse x -> aux f x.output
      )
    in
    aux f (Term x)

    let pp_meta f = function 
    | Constant None -> Fmt.pf f "<>" 
    | Constant (Some l) -> Fmt.pf f "<%s>" l
    | Map_input { source = _; info = Ok label } -> Fmt.string f label
    | Map_input { source = _; info = Error `Blocked } -> Fmt.string f "(blocked)"
    | Map_input { source = _; info = Error `Empty_list } -> Fmt.string f "(empty list)"
    | Opt_input _ -> Fmt.pf f "opt_input"
    | Bind_in _ -> Fmt.pf f "bind_in"
    | Bind_out _ -> Fmt.pf f "bind_out"
    | Primitive {info; _} -> Fmt.pf f "|>> %s" info
    | Pair _ -> Fmt.pf f "pair"
    | Gate_on _ -> Fmt.pf f "gate"
    | List_map _ -> Fmt.pf f "list map" 
    | Option_map _ -> Fmt.pf f "option map" 
    | State _ -> Fmt.pf f "state"
    | Catch _ -> Fmt.pf f "catch"
    | Map _ -> Fmt.pf f "mpa"
    | Collapse _ -> Fmt.pf f "collapse"

  module Node_set = Set.Make(struct type t = int let compare = compare end)

  module Out_node = struct
    (* Information about one node in the OCurrent graph. *)

    type t = {
      outputs : Node_set.t;
      (* Normally, this will be a singleton set containing just the node being
         considered. However, sometimes we choose to hide nodes. For example,
         if we have a node C representing the pair of A and B then we don't bother
         adding a dot node for C. Instead, C is represented by an `Out_node` with
         `outputs = {A, B}`. Anything that takes input from C will instead take
         input directly from both A and B. *)

      trans : Node_set.t;
      (* The set of nodes which must be resolved for this node to be resolved,
         excluding [outputs]. For example, in the graph `A -> B -> C`:

         trans(A) = {}
         trans(B) = {A}
         trans(C) = {A, B}

         This is used to hide edges that are implied by other edges, to simplify
         the output. *)
    }

    let empty = {
      outputs = Node_set.empty;
      trans = Node_set.empty;
    }

    let is_empty t = Node_set.is_empty t.outputs

(*
    let pp_set f ns =
      Fmt.(list ~sep:(unit ",") int) f (Node_set.elements ns)

    let pp f {outputs; trans} =
      Fmt.pf f "%a(%a)" pp_set outputs pp_set trans
*)

    (* The union of A and B's outputs and transitive dependencies,
       except that we remove outputs that are already dependencies
       of the other branch. *)
    let union a b =
      let outputs =
        Node_set.union
          (Node_set.filter (fun x -> not (Node_set.mem x b.trans)) a.outputs)
          (Node_set.filter (fun x -> not (Node_set.mem x a.trans)) b.outputs)
      in
      let outputs =
        if Node_set.is_empty outputs then a.outputs
        else outputs
      in {
        outputs;
        trans = Node_set.union a.trans b.trans;
      }

    (* Connect [t]'s outputs using [make_edge] to connect to something. *)
    let connect make_edge t =
      Node_set.iter make_edge t.outputs

    (* An ordinary node, represented by a single box in the diagram. *)
    let singleton ~deps i = {
      outputs = Node_set.singleton i;
      trans = Node_set.union deps.outputs deps.trans;
    }
  end

  let colour_of_activity = function
    | `Ready -> "#ffff00"
    | `Running -> "#ffa500"




  type dag = Seq of (string * dag list) | Par of dag list | Node of generic | Empty_node
  

  (* Given two nodes, returns the closest ancestor if it exists, or None. *)
  let get_common_ancestor t1 t2 =
    let ancestors_1 = ref Id.Map.empty in
    let ancestors_2 = ref Id.Map.empty 
    in
    let explore map_ref (Term t) = (* BFS *)
      let to_do = Queue.create () in 
      Queue.add (Term t, 0) to_do;
      while not (Queue.is_empty to_do) do 
        let (Term t, distance) = Queue.pop to_do in
        if Id.Map.mem t.id !map_ref then
          ()
        else
          map_ref := Id.Map.add t.id (Term t, distance) !map_ref;
          match t.ty with 
          | Primitive {x; _} -> Queue.add (x, distance+1) to_do
          | Pair (a1, a2) -> (Queue.add (a1, distance+1) to_do; Queue.add (a2, distance+1) to_do)
          | Gate_on {ctrl; value; _} -> (Queue.add (ctrl, distance+1) to_do; Queue.add (value, distance+1) to_do)
          | Map x -> Queue.add (x, distance+1) to_do
          | Bind_out v -> Queue.add (Current_incr.observe v, distance+1) to_do
          | Catch {source; _} -> Queue.add (source, distance+1) to_do
          | _ -> ()
      done
    in
    explore ancestors_1 t1;
    explore ancestors_2 t2;
    let common = Id.Map.merge 
    (fun _ d1 d2 -> match (d1,d2) with 
      | Some (t, d1), Some (_, d2) -> Some (t, d1+d2)
      | _ -> None) 
      !ancestors_1 
      !ancestors_2 
    in
    Id.Map.fold 
    (fun id (t, distance) -> function 
      | Some (min_id, (_, min_distance)) when distance > min_distance -> Some (min_id, (t, min_distance))
      | _ -> Some (id, (t, distance)))
      common
      None
    |> Option.map (fun (_, (t, _)) -> t) 
    
  let rec to_dag (Term t) stop_at =
    match stop_at with 
    | Some (Term t_stop) when t.id = t_stop.id -> (Printf.printf "the end\n%!"; Empty_node)
    | _ ->
    match t.ty with 
    | Primitive {x; info; _} -> (Printf.printf "primitive\n%!"; Seq (info, [to_dag x stop_at; Node (Term t)]))
    | Pair (a1, a2) -> 
      begin 
        Printf.printf "pair\n%!"; 
        match get_common_ancestor a1 a2 with 
        | None -> Par ([to_dag a1 stop_at; to_dag a2 stop_at])
        | Some node -> Seq ("pair", [to_dag node stop_at; Par ([to_dag a1 (Some node); to_dag a2 (Some node)])])
      end
    | Gate_on {ctrl; value; _} ->
      begin
        Printf.printf "gate_on\n%!"; 
        match get_common_ancestor ctrl value with 
        | None -> Par ([to_dag ctrl stop_at; to_dag value stop_at])
        | Some node -> Seq ("gate", [to_dag node stop_at; Par ([to_dag ctrl (Some node); to_dag value (Some node)])])
      end
    | Map next -> to_dag next stop_at
    | Bind_in (value, _) -> to_dag value stop_at
    | Bind_out value ->  to_dag (Current_incr.observe value) stop_at
    | Map_input _ -> (Printf.printf "Map_input\n%!"; Node (Term t))
    | Opt_input _ -> (Printf.printf "Opt_input\n%!"; Node (Term t))
    | State _ -> (Printf.printf "State\n%!"; Node (Term t))
    | Catch {source; label; _} -> (match t.bind with 
      | None -> Seq (label, [to_dag source stop_at])
      | Some ctx -> Seq (label, [to_dag ctx stop_at; to_dag source stop_at]))
    
    | List_map _ -> (Printf.printf "List_map\n%!"; Node (Term t))
    | Option_map _ -> (Printf.printf "Option_map\n%!"; Node (Term t))
    | Collapse _ -> (Printf.printf "Collapse\n%!"; Node (Term t))
    | Constant (Some _) -> (match t.bind with 
      | None -> Node (Term t)
      | Some ctx -> Seq ("cst", [to_dag ctx stop_at; Node (Term t)]))
    | Constant None -> (match t.bind with 
      | None -> Node (Term t)
      | Some ctx -> to_dag ctx stop_at)


  let remove_type =
    function 
  | Constant None -> true
  | _ -> false

  let rec simplify = function 
  | Node (Term t) when remove_type t.ty -> None
  | Empty_node -> None
  | Seq (lbl, lst) -> 
    let lst = List.filter_map simplify lst in
    (match lst with 
    | [] -> None
    | [Seq (_, lst)] -> Some (Seq (lbl, lst))
    | [v] -> Some v
    | lst -> Some (Seq (lbl, lst)))
  | Par lst ->
    let lst = List.filter_map simplify lst in
    (match lst with 
    | [] -> None
    | [v] -> Some v
    | lst -> Some (Par lst))
  | node -> Some node

  let rec flatten = function 
  | Seq (lbl, lst) ->
    let lst = List.map 
      (fun node -> match flatten node with 
        | Seq (_, lst) -> lst 
        | node -> [node])
      lst |> List.flatten in 
    Seq (lbl, lst)
  | Par lst ->
    let lst = List.map 
      (fun node -> match flatten node with 
        | Par lst -> lst 
        | node -> [node]) 
      lst |> List.flatten in 
    Par lst
  | Node n -> Node n 
  | Empty_node -> Empty_node


  type status = [`Done | `Ready | `Running | `Error | `Blocked]


  let int_of_status = function 
    | `Done -> 0
    | `Blocked -> 1
    | `Ready -> 2
    | `Running -> 3
    | `Error -> 4 
      

  let color_of_status = function 
    | `Done -> "#90ee90"
    | `Blocked -> "#d3d3d3"
    | `Error -> "#ff4500"
    | `Ready | `Running as x -> colour_of_activity x

  let get_term_status (Term t) : status =
    let v = Current_incr.observe t.v in 
    let error_from_self =
      match v with
      | Ok _ -> false
      | Error (id, _) when Id.equal id t.id -> true
      | Error (id, _) ->
        match t.ty with
        | Collapse { input = Term input; _} ->
          (* The error isn't from us. but this is a collapsed node. If we're just propagating
             an error from our input then keep that, but report errors from within the collapsed
             group as from us. *)
          begin match Current_incr.observe input.v with
            | Error (orig_id, _) -> not (Id.equal id orig_id)
            | Ok _ -> true
          end
        | _ -> false
    in
    match v with 
    | Ok _ -> `Done
    | Error _ when not error_from_self -> `Blocked (* Blocked *)
    | Error (_, `Active x) -> (x :> status)
    | Error (_, `Msg _) -> `Error

  let rec get_status = function 
    | Par lst | Seq (_, lst)  -> 
      let statuses = List.map get_status lst in
      let (v, _) = List.fold_left (fun (k,v) s  -> 
        let v2 = int_of_status s in 
        if v2 > v then (s, v2) else (k, v) ) (`Done, 0) statuses 
      in v
    | Node t -> get_term_status t
    | Empty_node -> `Error


  let rec pp_dag ~job_info f = function
    | Par lst -> begin 
      Fmt.pf f "<div>"; 
      List.iter (fun i -> Fmt.pf f "<div style='margin: 10px; padding-left: 16px; border-left: solid %s 3px'><div>%a</div></div>" (get_status i |> color_of_status) (pp_dag ~job_info) i) lst; 
      Fmt.pf f "</div>"
    end
    | Seq (lbl, lst) -> begin 
      Fmt.pf f "<details><summary>%s</summary><ol style='list-style: none;'>" lbl; 
      List.iteri (fun k i -> Fmt.pf f "<li><span style='color: %s'>%d) </span><div style='display: inline-block; vertical-align: top'>%a</div>" (get_status i |> color_of_status) (k+1) (pp_dag ~job_info) i) lst; 
      Fmt.pf f "</ol></details>"
    end
    | Node (Term t) -> (match t.ty with 
      | Primitive {info; meta; _} ->
        let _, url =
          match Current_incr.observe meta with
          | None -> None, None
          | Some id -> job_info id
        in
         Fmt.pf f "<a href='%a'>%s</a>" (Fmt.option Fmt.string) url info
      | Constant (Some str) -> Fmt.pf f ">%s" str
      | Constant None -> Fmt.pf f "><" 
      | meta -> Fmt.pf f "%a" pp_meta meta
    )
    | Empty_node -> ()

  let pp_html ~job_info f x = 
    let dag = to_dag (Term x) None |> simplify |> Option.get |> flatten in
    pp_dag ~job_info f dag

  let pp_dot ~env ~collapse_link ~job_info f x =
    let env = Env.of_seq (List.to_seq env) in
    let next = ref 0 in
    let seen : Out_node.t Id.Map.t ref = ref Id.Map.empty in
    let pending_edges = ref [] in
    let edge_to ?style ?color b a = pending_edges := (style, color, a, b) :: !pending_edges in
    let flush_pending () =
      !pending_edges |> List.iter (fun (style, color, a, b) -> Dot.edge f ?style ?color a b);
      pending_edges := []
    in
    let rec aux (Term t) =
      match Id.Map.find_opt t.id !seen with
      | Some x -> x
      | None ->
        let i = !next in
        incr next;
        let ctx =
          match t.bind with
          | None -> Out_node.empty
          | Some c -> aux c
        in
        let v = Current_incr.observe t.v in
        let error_from_self =
          match v with
          | Ok _ -> false
          | Error (id, _) when Id.equal id t.id -> true
          | Error (id, _) ->
            match t.ty with
            | Collapse { input = Term input; _} ->
              (* The error isn't from us. but this is a collapsed node. If we're just propagating
                 an error from our input then keep that, but report errors from within the collapsed
                 group as from us. *)
              begin match Current_incr.observe input.v with
                | Error (orig_id, _) -> not (Id.equal id orig_id)
                | Ok _ -> true
              end
            | _ -> false
        in
        let bg =
          match v with
          | Ok _ -> "#90ee90"
          | Error _ when not error_from_self -> "#d3d3d3" (* Blocked *)
          | Error (_, `Active x) -> colour_of_activity x
          | Error (_, `Msg _) -> "#ff4500"
        in
        let tooltip =
          match v with
          | Error (_, `Msg msg) when error_from_self -> Some msg
          | _ -> None
        in
        let node ?(bg=bg) ?url =
          Dot.node ~style:"filled" ~bg ?tooltip ?url f in
        let outputs =
          match t.ty with
          | Constant (Some l) -> node i l; Out_node.singleton ~deps:ctx i
          | Constant None when Out_node.is_empty ctx ->
            if Result.is_ok v then ctx
            else (
              node i (if error_from_self then "(const)" else "(input)");
              Out_node.singleton ~deps:ctx i
            )
          | Constant None -> ctx
          | Map_input { source; info } ->
            let label =
              match info with
              | Ok l -> l
              | Error `Blocked -> "(each item)"
              | Error `Empty_list -> "(empty list)"
            in
            node i label;
            let source = aux source in
            Out_node.connect (edge_to i) source;
            let deps = Out_node.union source ctx in
            Out_node.singleton ~deps i
          | Opt_input { source } ->
            aux source
          | Bind_in (x, name) ->
            let inputs =
              match t.ty with
              | Constant None -> Out_node.empty
              | _ -> aux x
            in
            node i name;
            let all_inputs = Out_node.union inputs ctx in
            Out_node.connect (edge_to i) all_inputs;
            Out_node.singleton ~deps:all_inputs i
          | Bind_out x -> aux (Current_incr.observe x)
          | Primitive {x; info; meta} ->
            let inputs =
              match x with
              | Term { ty = Constant None; _ } -> Out_node.empty
              | _ -> aux x
            in
            let update_status, url =
              match Current_incr.observe meta with
              | None -> None, None
              | Some id -> job_info id
            in
            let bg = update_status |> Option.map (fun s ->
                let up_bg = colour_of_activity s in
                Printf.sprintf "%s:%s" up_bg bg
              )
            in
            node ?bg ?url i info;
            let all_inputs = Out_node.union inputs ctx in
            Out_node.connect (edge_to i) all_inputs;
            Out_node.singleton ~deps:all_inputs i
          | Pair (x, y) ->
            Out_node.union (aux x) (aux y) |> Out_node.union ctx
          | Gate_on { ctrl; value } ->
            let ctrls = aux ctrl in
            let values = aux value in
            node i "" ~shape:"circle";
            ctrls |> Out_node.connect (edge_to i ~style:"dashed");
            let data_inputs = Out_node.union values ctx in
            Out_node.connect (edge_to i) data_inputs;
            let deps = Out_node.(union ctrls data_inputs) in
            Out_node.singleton ~deps i
          | Catch { source; hidden = true; _ }
          | State { source; hidden = true } ->
            aux source
          | State { source; hidden = false } ->
            let inputs = aux source in
            node i "state";
            Out_node.connect (edge_to i) inputs;
            (* Because a state node will be ready even when its inputs aren't, we shouldn't
               remove dependencies just because they're also dependencies of a state node.
               e.g. setting a GitHub status depends on knowing which commit is to be tested
               and the state of the build. We can know the state of the build (pending) without
               yet knowing the commit. So the set_state node can't run even though its
               state input is ready and transitively depends on knowing the commit. *)
            Out_node.singleton ~deps:Out_node.empty i
          | Catch { source; hidden = false; _ } ->
            let inputs = aux source in
            node i "catch";
            let all_inputs = Out_node.union inputs ctx in
            Out_node.connect (edge_to i) all_inputs;
            Out_node.singleton ~deps:all_inputs i
          | Map x ->
            let inputs = aux x in
            begin match v with
              | Error (_, `Msg _) when error_from_self ->
                (* Normally, we don't show separate boxes for map functions.
                   But we do if one fails. *)
                node i "map";
                let all_inputs = Out_node.union inputs ctx in
                Out_node.connect (edge_to i) all_inputs;
                Out_node.singleton ~deps:all_inputs i
              | _ ->
                aux x
            end
          | List_map { items; output } ->
            ignore (aux items);
            Dot.begin_cluster f i;
            let outputs = aux (Current_incr.observe output) in
            Dot.end_cluster f;
            outputs
          | Option_map { item; output } ->
            ignore (aux item);
            Dot.begin_cluster f i;
            Dot.pp_option f ("style", "dotted");
            let outputs = aux (Current_incr.observe output) in
            Dot.end_cluster f;
            outputs
          | Collapse { key; value; input; output } ->
            if Env.find_opt key env = Some value then aux output
            else (
              let inputs = aux input in
              let all_inputs = Out_node.union inputs ctx in
              let url = collapse_link ~k:key ~v:value in
              node ?url i "+";
              Out_node.connect (edge_to i) all_inputs;
              Out_node.singleton ~deps:all_inputs i
            )
        in
        seen := Id.Map.add t.id outputs !seen;
        outputs
    in
    Fmt.pf f "@[<v2>digraph pipeline {@,\
              node [shape=\"box\"]@,\
              rankdir=LR@,";
    let _ = aux (Term x) in
    flush_pending ();
    Fmt.pf f "}@]@."

  (* This is similar to [pp_dot], except that for each call to [node] we call [count] instead. *)
  let stat x =
    let seen : Out_node.t Id.Map.t ref = ref Id.Map.empty in
    let next = ref 0 in
    let ok = ref 0 in
    let ready = ref 0 in
    let running = ref 0 in
    let failed = ref 0 in
    let blocked = ref 0 in
    let rec aux (Term t) =
      match Id.Map.find_opt t.id !seen with
      | Some x -> x
      | None ->
        let i = !next in
        incr next;
        let ctx =
          match t.bind with
          | None -> Out_node.empty
          | Some c -> aux c
        in
        let v = Current_incr.observe t.v in
        let error_from_self =
          match v with
          | Error (id, _) -> Id.equal id t.id
          | Ok _ -> false
        in
        let count () =
          match v with
          | Ok _ -> incr ok
          | _ when not error_from_self -> incr blocked
          | Error (_, `Active `Ready) -> incr ready
          | Error (_, `Active `Running) -> incr running
          | Error (_, `Msg _) -> incr failed
        in
        let outputs =
          match t.ty with
          | Constant (Some _) -> count (); Out_node.singleton ~deps:ctx i
          | Constant None when Out_node.is_empty ctx ->
            if Result.is_ok v then ctx
            else (
              count ();
              Out_node.singleton ~deps:ctx i
            )
          | Constant None -> ctx
          | Map_input { source; info = _ } ->
            count ();
            let source = aux source in
            let deps = Out_node.union source ctx in
            Out_node.singleton ~deps i
          | Opt_input { source } ->
            aux source
          | Bind_in (x, _name) ->
            let inputs =
              match t.ty with
              | Constant None -> Out_node.empty
              | _ -> aux x
            in
            count ();
            let all_inputs = Out_node.union inputs ctx in
            Out_node.singleton ~deps:all_inputs i
          | Bind_out x -> aux (Current_incr.observe x)
          | Primitive {x; info = _; meta = _} ->
            let inputs =
              match x with
              | Term { ty = Constant None; _ } -> Out_node.empty
              | _ -> aux x
            in
            count ();
            let all_inputs = Out_node.union inputs ctx in
            Out_node.singleton ~deps:all_inputs i
          | Pair (x, y) ->
            Out_node.union (aux x) (aux y) |> Out_node.union ctx
          | Gate_on { ctrl; value } ->
            count ();
            let ctrls = aux ctrl in
            let values = aux value in
            let data_inputs = Out_node.union values ctx in
            let deps = Out_node.(union ctrls data_inputs) in
            Out_node.singleton ~deps i
          | State { source; hidden } ->
            let _ : Out_node.t = aux source in
            if not hidden then count ();
            Out_node.singleton ~deps:Out_node.empty i
          | Catch { source; hidden; _ } ->
            let inputs = aux source in
            if not hidden then count ();
            let all_inputs = Out_node.union inputs ctx in
            Out_node.singleton ~deps:all_inputs i
          | Map x ->
            let inputs = aux x in
            let all_inputs = Out_node.union inputs ctx in
            begin match v with
              | Error (_, `Msg _) when error_from_self ->
                count ();
                Out_node.singleton ~deps:all_inputs i
              | _ ->
                aux x
            end
          | List_map { items; output } ->
            ignore (aux items);
            aux (Current_incr.observe output)
          | Option_map { item; output } ->
            ignore (aux item);
            aux (Current_incr.observe output)
          | Collapse x ->
            aux x.output
        in
        seen := Id.Map.add t.id outputs !seen;
        outputs
    in
    ignore (aux (Term x));
    { S.ok = !ok; ready = !ready; running = !running; failed = !failed; blocked = !blocked  }
end
