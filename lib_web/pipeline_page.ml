open Tyxml.Html

let render_result = function
  | Ok () -> [txt "Success!"]
  | Error (`Active `Ready) -> [txt "Ready..."]
  | Error (`Active `Running) -> [txt "Running..."]
  | Error (`Msg msg) -> [txt ("ERROR: " ^ msg)]

let settings ctx config =
  let selected = Current.Config.get_confirm config in
  let levels =
    Current.Level.values
    |> List.map @@ fun level ->
    let s = Current.Level.to_string level in
    let msg = Fmt.str "Confirm if level >= %s" s in
    let sel = if selected = Some level then [a_selected ()] else [] in
    option ~a:(a_value s :: sel) (txt msg)
  in
  let csrf = Context.csrf ctx in
  form ~a:[a_action "/set/confirm"; a_method `Post] [
    select ~a:[a_name "level"] (
      let sel = if selected = None then [a_selected ()] else [] in
      option ~a:(a_value "none" :: sel) (txt "No confirmation required") :: List.rev levels
    );
    input ~a:[a_name "csrf"; a_input_type `Hidden; a_value csrf] ();
    input ~a:[a_input_type `Submit; a_value "Submit"] ();
  ]

let r ~engine = object
  inherit Resource.t

  val! can_get = `Viewer

  method! private get ctx =
    let config = Current.Engine.config engine in
    let pipeline = Current.Engine.pipeline engine in
    let { Current.Engine.value; jobs = _ } = Current.Engine.state engine in
    let job_info { Current.Metadata.job_id; update } =
      let url = job_id |> Option.map (fun id -> Fmt.str "/job/%s" id) in
      update, url 
    in
    let html, css = Current.Analysis.to_html_css ~job_info pipeline in
    Context.respond_ok ctx [
      style [Unsafe.data {|
      #pipeline_container {
        display: flex;
        flex-direction: row;
        height: calc(100vh - 40px);
      }

      #pipeline {
        height: calc(100vh - 40px);
        overflow: auto;
      }

      #logs_iframe {
        height: calc(100vh - 40px);
        flex: 1;
        border: none;
        border-left: solid gray 1px;
        padding-left: 10px;
        margin-left: 10px;
      }

      |}];
      div ~a:[a_id "pipeline_container"] [
        div ~a:[a_id "pipeline"] [
          html;
          h2 [txt "Result"];
          p (render_result value);
          h2 [txt "Settings"];
          settings ctx config;
        ];
        Unsafe.data "<iframe id='logs_iframe' ></iframe>"
      ];
      script (Unsafe.data {|
        let logs = document.getElementById("logs_iframe");

        function setLogsUrl(url) {
          logs.src = url;
        }
        |});
    ]

  method! nav_link = Some "New pipeline rendering"
end
