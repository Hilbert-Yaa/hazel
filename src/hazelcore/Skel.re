open Sexplib.Std;

[@deriving sexp]
type t('op) =
  | Placeholder(int)
  | BinOp(ErrStatus.t, 'op, t('op), t('op));

[@deriving sexp]
type range = (int, int);

let rec leftmost_op =
  fun
  | Placeholder(_) => None
  | BinOp(_, op, skel1, _) =>
    switch (leftmost_op(skel1)) {
    | Some(op1) => Some(op1)
    | None => Some(op)
    };

let rec rightmost_op =
  fun
  | Placeholder(_) => None
  | BinOp(_, op, _, skel2) =>
    switch (rightmost_op(skel2)) {
    | Some(op1) => Some(op1)
    | None => Some(op)
    };

let rec size = (skel: t(_)): int =>
  switch (skel) {
  | Placeholder(_) => 1
  | BinOp(_, _, skel1, skel2) => size(skel1) + size(skel2)
  };

let rec leftmost_tm_index = (skel: t(_)): int =>
  switch (skel) {
  | Placeholder(n) => n
  | BinOp(_, _, skel1, _) => leftmost_tm_index(skel1)
  };

let rec rightmost_tm_index = (skel: t(_)): int =>
  switch (skel) {
  | Placeholder(n) => n
  | BinOp(_, _, _, skel2) => rightmost_tm_index(skel2)
  };

let rec range = (skel: t(_)): range =>
  switch (skel) {
  | Placeholder(n) => (n, n)
  | BinOp(_, _, skel1, skel2) =>
    let (a, _) = range(skel1);
    let (_, b) = range(skel2);
    (a, b);
  };

// return bool is for internal use,
// indicates whether the accompanying
// skel is the target subskel
let rec _subskel_rooted_at_op =
        (op_index: OpIndex.t, skel: t('op)): (bool, t('op)) =>
  switch (skel) {
  | Placeholder(_) => (false, skel)
  | BinOp(_, _, skel1, skel2) =>
    let (found1, subskel1) = _subskel_rooted_at_op(op_index, skel1);
    let (found2, subskel2) = _subskel_rooted_at_op(op_index, skel2);
    switch (found1, found2) {
    | (true, _) => (true, subskel1)
    | (_, true) => (true, subskel2)
    | (false, false) => (leftmost_tm_index(subskel2) == op_index, skel)
    };
  };
let subskel_rooted_at_op = (op_index: OpIndex.t, skel: t('op)): t('op) => {
  let (_, subskel) = _subskel_rooted_at_op(op_index, skel);
  subskel;
};

let mk =
    (
      precedence: 'op => int,
      associativity: 'op => Associativity.t,
      seq: Seq.t('operand, 'op),
    )
    : t('op) => {
  /**
   * Shunting-yard opp algorithm according to the specification here
   * https://en.wikipedia.org/wiki/Shunting-yard_algorithm#The_algorithm_in_detail
   *
   */
  let rec go_seq =
          (
            skel_stack: list(t('op)), /* List of skels to be combined into single output skel. */
            op_stack: list('op), /* Stack of operators. */
            seq: Seq.t('operand, 'op), /* Convert this seq to output skel. */
            lex_addr: int,
          ) /* Lexical address of the current operand. */
          : t('op) => {
    switch (seq) {
    | S(_, affix) =>
      /**
       * If the next token is an operand, add a new operand to the output skel.
       */
      go_affix(
        [Placeholder(lex_addr), ...skel_stack],
        op_stack,
        affix, /* Tail of seq without first operand. */
        lex_addr + 1 /* Increment lexical address of operand in seq. */
      )
    };
  }
  and go_affix =
      (
        skel_stack: list(t('op)),
        op_stack: list('op),
        affix: Seq.affix('operand, 'op),
        lex_addr: int,
      )
      : t('op) => {
    switch (affix) {
    | A(op, seq) =>
      /**
       * If the next token is an operator, pop operators from the operator stack,
       * then push this operator to the operator stack.
       */
      let should_mv = op' =>
        /**
         * Continue popping operators while the precedence of the top of the operator
         * stack has greater precedence than the current operator.
         *
         * Either the operator on the top of the stack is left associative and
         * has greater or equal precedence to the current operator, or the
         * operator on the top of the stack is right associative and has strictly
         * greater precedence to the current operator.
         */
        {
          switch (associativity(op')) {
          | Associativity.Left => precedence(op) <= precedence(op')
          | Associativity.Right => precedence(op) < precedence(op')
          };
        };

      let (skel_stack', op_stack') =
        build_ast_while(skel_stack, op_stack, should_mv);

      /* Push this operator to the operator stack. */
      go_seq(skel_stack', [op, ...op_stack'], seq, lex_addr);
    | E =>
      /**
       * Once the input seq is empty, continuously pop
       * operators in the stack and build up the output skel.
       */
      let (skel_stack', _) = build_ast_while(skel_stack, op_stack, _ => true);
      switch (skel_stack') {
      | [final_skel] => final_skel // In this case,
      | _ => failwith("Error: Skel parser called with invalid operands")
      };
    };
  }
  and build_ast_while =
      (skel_stack: list(t('op)), op_stack: list('op), should_mv)
      : (list(t('op)), list('op)) => {
    /* Move operators from the operator stack to the output skel list while... */
    switch (op_stack, skel_stack) {
    | ([], _) => (skel_stack, op_stack) /* (1) The operator stack is not empty. */
    | ([op, ...op_stack'], [subskel1, subskel2, ...skel_stack'])
        when should_mv(op) =>
      /**  (2) See defn of should_mv in go_affix.
         *       Note - This impl supports only binary operators.
         *
         * Example -
         *
         * skels:
         * [Placeholder(0) Placeholder(1)]
         *
         * op_stack:
         * [Plus]
         *
         * -->
         *
         * skels:
         * [BinOp(_, Plus, Placeholder(1), Placeholder(0))]
         *
         * op_stack:
         * []
         *
         */
      build_ast_while(
        [BinOp(ErrStatus.NotInHole, op, subskel2, subskel1), ...skel_stack'],
        op_stack',
        should_mv,
      )
    | _ => (skel_stack, op_stack)
    };
  };
  go_seq([], [], seq, 0);
};
