def transform(x):
    return x % 64 + (x // 128) * 64
