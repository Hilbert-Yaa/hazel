open Virtual_dom;

/**
 * Raised when a selected hole instance does not exist.
 * Indicates a bug.
 */
exception InvalidInstance;

/**
 * Panel showing the typing context and environment at the cursor.
 */
let view: (~inject: ModelAction.t => Vdom.Event.t, Model.t) => Vdom.Node.t;
