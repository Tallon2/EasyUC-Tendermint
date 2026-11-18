ec_requires +Int +List FSet +SingleRound.

direct RoundClient {
  in client@start(ids : int list, weights : (int * int) list, bad : int list, leader : int, candidate : int)
  out decide(node : int, block : int)@client
}
direct RoundIO { D : RoundClient }

adversarial SchedulerPort {
  out ready
  in action(kind : int, origin : int, recipient : int, phase : int, block : int)
  out status(accepted : bool)
  in inspect(node : int, phase : int, block : int)
  out observed(weight : int)
}
adversarial Scheduler { A : SchedulerPort }

functionality Round implements RoundIO Scheduler {
  party Machine serves RoundIO.D Scheduler.A {
    initial state Init {
      match message with
      | client@RoundIO.D.start(ids,weights,bad,leader,candidate) => {
          if (configured ids weights bad leader) {
            send Scheduler.A.ready and transition Run(client,ids,weights,bad,(leader,candidate),empty_history).
          } else { fail. }
        }
      end
    }
    state Run(client : port, ids : int list, weights : (int * int) list,
              bad : int list, proposal : int * int, s : history) {
      var e : event;
      var ok : bool;
      var next : history;
      match message with
      | Scheduler.A.action(kind,origin,recipient,phase,block) => {
          e <- (kind,origin,recipient,phase,block);
          ok <- enabled ids (stake_at weights) (FSet.oflist bad) proposal s e;
          next <- step ids (stake_at weights) (FSet.oflist bad) proposal s e;
          if (kind = 2 /\ ok) {
            send RoundIO.D.decide(origin,block)@client
              and transition Run(client,ids,weights,bad,proposal,next).
          } else {
            send Scheduler.A.status(ok)
              and transition Run(client,ids,weights,bad,proposal,next).
          }
        }
      | Scheduler.A.inspect(node,phase,block) => {
          send Scheduler.A.observed(tally ids (stake_at weights) s node phase block)
            and transition Run(client,ids,weights,bad,proposal,s).
        }
      | * => { fail. }
      end
    }
  }
}

(* This mirror and relay satisfy the interpreter's unit structure.
   The agreement theorem concerns the shared transition function. *)
adversarial RoundToRelay {
  out ready
  in action(kind : int, origin : int, recipient : int, phase : int, block : int)
  out status(accepted : bool)
  in inspect(node : int, phase : int, block : int)
  out observed(weight : int)
}
functionality RoundMirror implements RoundIO RoundToRelay {
  initial state Init {
    match message with
    | client@RoundIO.D.start(ids,weights,bad,leader,candidate) => {
        if (configured ids weights bad leader) {
          send RoundToRelay.ready and transition Run(client,ids,weights,bad,(leader,candidate),empty_history).
        } else { fail. }
      }
    end
  }
  state Run(client : port, ids : int list, weights : (int * int) list,
            bad : int list, proposal : int * int, s : history) {
    var e : event;
    var ok : bool;
    var next : history;
    match message with
    | RoundToRelay.action(kind,origin,recipient,phase,block) => {
        e <- (kind,origin,recipient,phase,block);
        ok <- enabled ids (stake_at weights) (FSet.oflist bad) proposal s e;
        next <- step ids (stake_at weights) (FSet.oflist bad) proposal s e;
        if (kind = 2 /\ ok) {
          send RoundIO.D.decide(origin,block)@client
            and transition Run(client,ids,weights,bad,proposal,next).
        } else {
          send RoundToRelay.status(ok)
            and transition Run(client,ids,weights,bad,proposal,next).
        }
      }
    | RoundToRelay.inspect(node,phase,block) => {
        send RoundToRelay.observed(tally ids (stake_at weights) s node phase block)
          and transition Run(client,ids,weights,bad,proposal,s).
      }
    | * => { fail. }
    end
  }
}

simulator RoundRelay uses RoundToRelay simulates Round {
  initial state Init {
    match message with
    | RoundToRelay.ready => {
        send Round.Scheduler.A.ready and transition Relay.
      }
    | * => { fail. }
    end
  }
  state Relay {
    match message with
    | Round.Scheduler.A.action(kind,origin,recipient,phase,block) => {
        send RoundToRelay.action(kind,origin,recipient,phase,block) and transition Relay.
      }
    | Round.Scheduler.A.inspect(node,phase,block) => {
        send RoundToRelay.inspect(node,phase,block) and transition Relay.
      }
    | RoundToRelay.status(ok) => {
        send Round.Scheduler.A.status(ok) and transition Relay.
      }
    | RoundToRelay.observed(w) => {
        send Round.Scheduler.A.observed(w) and transition Relay.
      }
    | * => { fail. }
    end
  }
}
