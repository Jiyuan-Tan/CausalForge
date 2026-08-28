node assignment-law | Assignment law P
node block-a | Block sum S_A
node block-b | Block sum S_B
node covariance | Covariance X(u,v) | two-block covariance
node coords | Spectral coords | x within spread | y contrast; z_sp balance
node simplex | Relaxed problem | weighted simplex | in x,y,z_sp
node parity | Parity condition | finite condition | odd m: odd sums
node check | Implementability check | implementable slice
edge assignment-law -> block-a
edge assignment-law -> block-b
edge block-a -> covariance
edge block-b -> covariance
edge covariance -> coords
edge coords -> simplex
edge block-a -> parity
edge block-b -> parity
edge coords -> check
edge parity -> check
