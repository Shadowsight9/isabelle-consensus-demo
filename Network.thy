section ‹Network model›

text ‹We define a simple model of a distributed system. The system consists of
a set of processes, each of which has a unique identifier and local state that
it can update. There is no shared state between processes; processes can
communicate only by sending messages to each other. The communication is
\emph{asynchronous} -- that is, messages may be delayed arbitrarily,
reordered, duplicated, or dropped entirely.

In reality, processes execute concurrently, possibly at different speeds (in
particular, a process may fail by stopping execution entirely). To model this,
we say that the system as a whole makes progress by one of the processes
performing an execution step, and processes may perform steps in any order.

An execution step involves a process handling an \emph{event}. An event could
be one of several things: a request from a user, receiving a message from
another process, or the elapsing of a timeout. In response to such an event,
a process can update its local state, and/or send messages to other processes.›

theory
  Network
imports
  Main
begin


text ‹A message is always sent to a particular recipient. This datatype
encapsulates the name of the recipient process and the message being sent.›

datatype ('proc, 'msg) send
  = Send (msg_recipient: 'proc) (send_msg: 'msg)


text ‹An event that a process may handle: receiving a message from another
process, or a request from a user, or an elapsed timeout.›

datatype ('proc, 'msg, 'val) event
  = Receive (msg_sender: 'proc) (recv_msg: 'msg)
  | Request 'val
  | Timeout


text ‹A step function takes three arguments: the name of the process that is
executing, its current local state, and the event being handled. It returns two
things: the new local state, and a set of messages to send to other processes.›

type_synonym ('proc, 'state, 'msg, 'val) step_func =
  ‹'proc ⇒ 'state ⇒ ('proc, 'msg, 'val) event ⇒ ('state × ('proc, 'msg) send set)›


text ‹A process may only receive a message from a given sender if that sender
process did previously send that message. Request and Timeout events can occur
at any time.›

fun valid_event :: ‹('proc, 'msg, 'val) event ⇒ 'proc ⇒
                    ('proc × ('proc, 'msg) send) set ⇒ bool› where
  ‹valid_event (Receive sender msg) proc msgs = ((sender, Send proc msg) ∈ msgs)› |
  ‹valid_event (Request _) _ _ = True› |
  ‹valid_event Timeout _ _ = True›


text ‹A valid execution of a distributed algorithm is a sequence of execution
steps. At each step, any of the processes handles any valid event. We call the
step function to compute the next state for that process, and any messages it
sends are added to a global set of all messages ever sent.›

inductive execute ::
    ‹('proc, 'state, 'msg, 'val) step_func ⇒ ('proc ⇒ 'state) ⇒ 'proc set ⇒
     ('proc × ('proc, 'msg, 'val) event) list ⇒
     ('proc × ('proc, 'msg) send) set ⇒ ('proc ⇒ 'state) ⇒ bool› where
  ‹execute step init procs [] {} init› |
  ‹⟦execute step init procs events msgs states;
    proc ∈ procs;
    valid_event event proc msgs;
    step proc (states proc) event = (new_state, sent);
    events' = events @ [(proc, event)];
    msgs' = msgs ∪ ((λmsg. (proc, msg)) ` sent);
    states' = states (proc := new_state)
   ⟧ ⟹ execute step init procs events' msgs' states'›


subsection ‹Lemmas for the network model›

text ‹We prove a few lemmas that are useful when working with the above network model.›

inductive_cases execute_indcases: ‹execute step init procs events msg states›

lemma execute_init:
  assumes ‹execute step init procs [] msgs states›
  shows ‹msgs = {} ∧ states = init›
  using assms by(auto elim: execute.cases)

inductive_cases execute_snocE [elim!]:
  ‹execute step init procs (events @ [(proc, event)]) msgs' states'›

lemma execute_step:
  assumes ‹execute step init procs (events @ [(proc, event)]) msgs' states'›
  shows ‹∃msgs states sent new_state.
          execute step init procs events msgs states ∧
          proc ∈ procs ∧
          valid_event event proc msgs ∧
          step proc (states proc) event = (new_state, sent) ∧
          msgs' = msgs ∪ ((λmsg. (proc, msg)) ` sent) ∧
          states' = states (proc := new_state)›
  using assms by auto

lemma execute_receive:
  assumes ‹execute step init procs (events @ [(recpt, Receive sender msg)]) msgs' states'›
  shows ‹(sender, Send recpt msg) ∈ msgs'›
  using assms execute_step by fastforce

end