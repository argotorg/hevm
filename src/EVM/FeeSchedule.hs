module EVM.FeeSchedule where

data FeeSchedule n = FeeSchedule
  { g_zero :: n
  , g_base :: n
  , g_verylow :: n
  , g_low :: n
  , g_mid :: n
  , g_high :: n
  , g_extcode :: n
  , g_balance :: n
  , g_sload :: n
  , g_jumpdest :: n
  , g_sset :: n
  , g_sreset :: n
  , r_sclear :: n
  , g_selfdestruct :: n
  , g_selfdestruct_newaccount :: n
  , r_selfdestruct :: n
  , g_create :: n
  , g_codedeposit :: n
  , g_call :: n
  , g_callvalue :: n
  , g_callstipend :: n
  , g_newaccount :: n
  , g_exp :: n
  , g_expbyte :: n
  , g_memory :: n
  , g_txcreate :: n
  , g_txdatazero :: n
  , g_txdatanonzero :: n
  , g_transaction :: n
  , g_log :: n
  , g_logdata :: n
  , g_logtopic :: n
  , g_sha3 :: n
  , g_sha3word :: n
  , g_initcodeword :: n
  , g_copy :: n
  , g_blockhash :: n
  , g_extcodehash :: n
  , g_quaddivisor :: n
  , g_ecadd :: n
  , g_ecmul :: n
  , g_pairing_point :: n
  , g_pairing_base :: n
  , g_fround :: n
  , r_block :: n
  , g_cold_sload :: n
  , g_cold_account_access :: n
  , g_warm_storage_read :: n
  , g_access_list_address :: n
  , g_access_list_storage_key :: n
  , g_txdatafloor :: n
  , g_auth_base :: n              -- EIP-7702: base cost per authorization
  -- EIP-4844
  , g_point_evaluation :: n
  } deriving Show

feeSchedule :: Num n => FeeSchedule n
feeSchedule = FeeSchedule
  { g_zero = 0
  , g_base = 2
  , g_verylow = 3
  , g_low = 5
  , g_mid = 8
  , g_high = 10
  , g_extcode = 2600
  , g_balance = 2600
  , g_sload = 100
  , g_jumpdest = 1
  , g_sset = 20000
  , g_sreset = 2900
  , r_sclear = 15000
  , g_selfdestruct = 5000
  , g_selfdestruct_newaccount = 25000
  , r_selfdestruct = 24000
  , g_create = 32000
  , g_codedeposit = 200
  , g_call = 2600
  , g_callvalue = 9000
  , g_callstipend = 2300
  , g_newaccount = 25000
  , g_exp = 10
  , g_expbyte = 50
  , g_memory = 3
  , g_txcreate = 32000
  , g_txdatazero = 4
  , g_txdatanonzero = 16
  , g_transaction = 21000
  , g_log = 375
  , g_logdata = 8
  , g_logtopic = 375
  , g_sha3 = 30
  , g_sha3word = 6
  , g_initcodeword = 2
  , g_copy = 3
  , g_blockhash = 20
  , g_extcodehash = 2600
  , g_quaddivisor = 20
  , g_ecadd = 150
  , g_ecmul = 6000
  , g_pairing_point = 34000
  , g_pairing_base = 45000
  , g_fround = 1
  , r_block = 2000000000000000000
  , g_cold_sload = 2100
  , g_cold_account_access = 2600
  , g_warm_storage_read = 100
  , g_access_list_address = 2400
  , g_access_list_storage_key = 1900
  , g_txdatafloor = 10
  , g_auth_base = 12500           -- EIP-7702: PER_AUTH_BASE_COST
  -- EIP-4844
  , g_point_evaluation = 50000
  }
