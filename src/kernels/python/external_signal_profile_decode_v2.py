# Map wire bits to the semantic profile word; collapse reserved inputs to a sentinel.
def transform(x): return (((x & 3) << 5) | ((x & 12) << 1) | ((x & 16) >> 2) | ((x & 32) >> 4) | ((x & 64) >> 6)) if x < 128 else 255
