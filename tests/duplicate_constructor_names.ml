module Error = struct
  type invalid_block =
    | Gas_above_limit
    | Invalid_number

  type invalid_transaction =
    | Gas_above_limit
    | Invalid_nonce

  let block_error : invalid_block = Gas_above_limit
  let transaction_error : invalid_transaction = Gas_above_limit

  let is_block_gas_error (error : invalid_block) =
    match error with
    | Gas_above_limit -> true
    | Invalid_number -> false

  let is_transaction_gas_error (error : invalid_transaction) =
    match error with
    | Gas_above_limit -> true
    | Invalid_nonce -> false
end
