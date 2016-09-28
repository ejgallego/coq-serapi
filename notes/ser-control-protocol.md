# SerAPI control protocol

This document defines the SerAPI control protocol. It is based on the
Coq XML protocol plus many discussions with developers.

The goal of the protocol is to allow IDEs to be as stateless as
possible. To this extent, the IDE should generally react to relevant
user input by sending the proper Coq command and forgetting about it.

Coq is allowed to notify about the results of these commands (if any)
arbitrary long. Arbitrary commands can be queued, and Coq must
interact properly on all use cases.

## Document Building / Maintenance

A document is build by adding/cancelling nodes. Each node corresponds to a Coq sentence. `nid` 

### Commands

- `Add(after, nid, text)`: Adds a new node `nid` to the document after node `after`.
  It will result in a parsing error or in a confirmation of proper parsing.
- `Cancel(nid)`: Informs Coq the node `nid` is no longer valid.
  It will invariably succeed.
- `Observe(nid)`: "Observes" (executes) until node `nid`.
  It may produce much feedback, including errors.

### Responses/Feedback

- `Added(nid, loc)`: Informs the UI that node `nid` was successfully parsed.
- `Errored(nid, msg)`: Informs the UI that node `nid` fatally
  failed. It must be added again _XXX: should we require cancellation
  of a failed node? keep in mind that there exist non-fatal errors
  that indeed must be cancelled_
- `Cancelled(nid_list)`: Informs the UI that the `nid_list` nodes are no longer valid.
- `Message(nid, msg)`: Informs of non-fatal errors, warnings, debug information.
- Rest of feedback: processed, ready, etc...

### Whole Document Parsing

`Add(after, nid, text)`: Can also have a whole document parsing. In
this case, the returned `nid` will be appended a number starting with `0`.

Thus, one add can generate many `Added`.

### Interrupting

1. The IDE must send an interrupt signal to sertop.
1. The IDE must process all the pending feedback until getting the Break message.
1. The IDE must then cancel non-desired states.

### Error Handling

- Is an errored state cancelled?
- Is it a bug in Coq to produce an exception but not an err msg?

### Use cases / Examples

- UI edit after add: The user sends a sentence, to immediate edit
  it. In this case, the IDE sends `Added(nid)` + `Cancel(nid)`, no
  need to wait.

## Acknowledgments

Clément Pit--Claudel, Enrico Tassi
