module Types {
  datatype Event =
    | GetEvent(key: int, value: int)
    | PutEvent(key: int, value: int)
    | NoOpEvent()
}
