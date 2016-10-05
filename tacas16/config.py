import numpy as np
from scipy.sparse import csr_matrix, csc_matrix

# Matrix representation
DENSE  = 'dense'
SPARSE = 'sparse'

representation_mode = DENSE
sparse_type = 'csr'
sparse_matrix = csr_matrix if sparse_type == 'csr' else csc_matrix

# Updates precision
precision = np.int8

# Parallelism
parallel = False

# Verbosity
verbose = False
