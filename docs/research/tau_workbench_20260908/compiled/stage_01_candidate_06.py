def transform(x):
    return (x & 63) | ((x & 128) >> 1)
