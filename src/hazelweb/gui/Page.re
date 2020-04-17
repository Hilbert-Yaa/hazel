module Js = Js_of_ocaml.Js;
module Vdom = Virtual_dom.Vdom;

let examples_select = (~inject: Update.Action.t => Vdom.Event.t) =>
  Vdom.(
    Node.select(
      [
        Attr.on_change((_, example_id) =>
          inject(Update.Action.LoadExample(example_id))
        ),
      ],
      [
        Node.option([Attr.value("just_hole")], [Node.text("just a hole")]),
        Node.option(
          [Attr.value("holey_lambda")],
          [Node.text("holey lambda")],
        ),
        Node.option(
          [Attr.value("let_line")],
          [Node.text("let with extra lines")],
        ),
        Node.option([Attr.value("map_example")], [Node.text("map")]),
        Node.option([Attr.value("qsort_example")], [Node.text("qsort")]),
      ],
    )
  );

let cardstacks_select =
    (
      ~inject: Update.Action.t => Vdom.Event.t,
      cardstacks: list(CardstackInfo.t),
    ) => {
  let cardstack_options =
    List.mapi(
      (i, cardstack: CardstackInfo.t) => {
        let example_idx = string_of_int(i);
        Vdom.(
          Node.option(
            [Attr.value(example_idx)],
            [Node.text(cardstack.title)],
          )
        );
      },
      cardstacks,
    );
  Vdom.(
    Node.select(
      [
        Attr.on_change((_, example_idx) =>
          inject(Update.Action.LoadCardstack(int_of_string(example_idx)))
        ),
      ],
      cardstack_options,
    )
  );
};

let prev_card_button = (~inject, model: Model.t) => {
  let cardstack = model |> Model.get_cardstack;
  let show_prev = Cardstack.has_prev(cardstack) ? [] : [Vdom.Attr.disabled];
  Vdom.(
    Node.button(
      [
        Attr.id("cardstack-prev-button"),
        Attr.on_click(_ => inject(Update.Action.PrevCard)),
        ...show_prev,
      ],
      [Node.text("Previous")],
    )
  );
};

let next_card_button = (~inject, model: Model.t) => {
  let cardstack = model |> Model.get_cardstack;
  let show_next = Cardstack.has_next(cardstack) ? [] : [Vdom.Attr.disabled];
  Vdom.(
    Node.button(
      [
        Attr.id("cardstack-next-button"),
        Attr.on_click(_ => inject(Update.Action.NextCard)),
        ...show_next,
      ],
      [Node.text("Next")],
    )
  );
};

let cardstack_controls = (~inject, model: Model.t) =>
  Vdom.(
    Node.div(
      [Attr.id("cardstack-controls")],
      [
        Node.div(
          [Attr.id("button-centering-container")],
          [
            prev_card_button(~inject, model),
            next_card_button(~inject, model),
          ],
        ),
      ],
    )
  );

let view = (~inject: Update.Action.t => Vdom.Event.t, model: Model.t) => {
  TimeUtil.measure_time("Page.view", () => {
    open Vdom;
    let card = model |> Model.get_card;
    let program = model |> Model.get_program;
    let cell_status =
      if (!model.compute_results.compute_results) {
        Node.div([], []);
      } else {
        Node.div(
          [],
          [
            Node.div(
              [Attr.classes(["cell-status"])],
              [
                Node.div(
                  [Attr.classes(["type-indicator"])],
                  [
                    Node.div(
                      [Attr.classes(["type-label"])],
                      [Node.text("Result of type: ")],
                    ),
                    Node.div(
                      [Attr.classes(["htype-view"])],
                      [
                        {
                          let (_, ty, _) = program |> Program.get_edit_state;
                          HTypCode.view(ty);
                        },
                      ],
                    ),
                  ],
                ),
              ],
            ),
            Node.div(
              [Attr.classes(["result-view"])],
              [
                DHCode.view(
                  ~inject,
                  ~show_fn_bodies=model.compute_results.show_fn_bodies,
                  ~show_case_clauses=model.compute_results.show_case_clauses,
                  ~show_casts=model.compute_results.show_casts,
                  ~selected_instance=model |> Model.get_selected_hole_instance,
                  ~width=80,
                  model.compute_results.show_unevaluated_expansion
                    ? program |> Program.get_expansion
                    : program |> Program.get_result |> Result.get_dhexp,
                ),
              ],
            ),
          ],
        );
      };
    let e = program |> Program.get_uhexp;
    let doc =
      lazy(
        Lazy.force(
          UHDoc.Exp.mk,
          ~memoize=model.memoize_doc,
          ~enforce_inline=false,
          e,
        )
      );
    let layout =
      lazy(
        switch (
          Pretty.LayoutOfDoc.layout_of_doc(
            Lazy.force(doc),
            ~width=80,
            ~pos=0,
          )
        ) {
        | None => Pretty.Layout.Text("layout FAILED") // TODO
        | Some(l) => l
        }
      );
    let box = lazy(Pretty.BoxOfLayout.box_of_layout(Lazy.force(layout)));
    Node.div(
      [Attr.id("root")],
      [
        Node.div(
          [Attr.classes(["top-bar"])],
          [
            Node.a(
              [Attr.classes(["logo-text"]), Attr.href("https://hazel.org")],
              [Node.text("Hazel")],
            ),
            cardstacks_select(~inject, Model.cardstack_info),
          ],
        ),
        Node.div(
          [Attr.classes(["main-area"])],
          [
            /*
             Sidebar.left(
               ~inject,
               model,
               [ActionPanel.view(~inject, model)] //the_history_panel,
             ),
             */
            Node.div(
              [Attr.classes(["flex-wrapper"])],
              [
                Node.div(
                  [Attr.id("page-area")],
                  [
                    Node.div(
                      [Attr.classes(["page"])],
                      [
                        Node.div(
                          [Attr.classes(["card-caption"])],
                          [card.info.caption],
                          /* [
                               Node.text("Hazel is an experiment in "),
                               Node.strong(
                                 [],
                                 [Node.text("live functional programming")],
                               ),
                               Node.text(" with "),
                               Node.strong([], [Node.text("typed holes")]),
                               Node.text(
                                 ". Use the actions on the left to construct an expression. Navigate using the text cursor in the usual way.",
                               ),
                             ], */
                        ),
                        Cell.view(~inject, model),
                        cell_status,
                        cardstack_controls(~inject, model),
                      ],
                    ),
                    examples_select(~inject),
                    Node.button(
                      [
                        Attr.on_click(_ => {
                          let e = program |> Program.get_uhexp;
                          JSUtil.log(Js.string(Serialize.string_of_exp(e)));
                          Event.Ignore;
                        }),
                      ],
                      [Node.text("Serialize to console")],
                    ),
                    Node.div(
                      [
                        Attr.style(
                          Css_gen.(
                            white_space(`Pre) @> font_family(["monospace"])
                          ),
                        ),
                      ],
                      if (!model.show_presentation) {
                        [];
                      } else {
                        [JSUtil.vdom_of_box(Lazy.force(box))];
                      },
                    ),
                  ],
                ),
              ],
            ),
            Sidebar.right(
              ~inject,
              model,
              [
                CursorInspector.view(model),
                ContextInspector.view(~inject, model),
                OptionsPanel.view(~inject, model),
              ],
            ),
          ],
        ),
      ],
    );
  });
};
