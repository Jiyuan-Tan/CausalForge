node exact-source | Exact source | binary homogeneity | collision baseline
node affine-embedding | Affine embedding | real outcomes | scale M
node exact-lower | Exact lower | baseline lower bound | data processing
node radius-source | Radius source | binary alternatives
node attenuation | Attenuation | σ/2 channel | data processing
node radius-family | Radius family | real outcomes | inside σM radius
node radius-lower | Radius lower | channel lower bound
edge exact-source -> affine-embedding
edge affine-embedding -> exact-lower
edge radius-source -> attenuation
edge attenuation -> radius-family
edge radius-family -> radius-lower
