# Map the semantic profile word to wire bits; collapse reserved inputs to a sentinel.
def transform(x): return ((x >> 5) | ((x & 24) >> 1) | ((x & 4) << 2) | ((x & 2) << 4) | ((x & 1) << 6)) if x < 128 else 255
