Definition is_some {A} (o:option A) : bool
  := 
  match o with 
  | Some _ => true
  | _ => false
  end.
