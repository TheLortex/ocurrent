(* Static analysis of a build pipeline. *)

module Make (Metadata : sig type t end) : sig
  type 'a t

  val stat : _ t -> S.stats

  val pp : _ t Fmt.t
  val pp_dot :
    env:(string * string) list ->
    collapse_link:(k:string -> v:string -> string option) ->
    job_info:(Metadata.t -> Output.active option * string option) ->
    _ t Fmt.t
  val to_html_css : job_info:(Metadata.t -> Output.active option * string option) -> _ t -> ([ | Html_types.div_content_fun] Tyxml.Html.elt * string)
end with type 'a t := 'a Node.Make(Metadata).t
