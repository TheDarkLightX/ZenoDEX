#!/usr/bin/env julia

using Pkg
using Random

if "--install" in ARGS
    Pkg.add("Metal")
end

try
    @eval using Metal
catch err
    println("Metal.jl is not available in this Julia environment.")
    println("Run: julia --project=tools/macos_scout tools/macos_scout/metal_smoke.jl --install")
    rethrow(err)
end

println("Metal.jl version info:")
Metal.versioninfo()

rng = MersenneTwister(20260508)
cpu = rand(rng, Float32, 4096)
gpu = MtlArray(cpu)
roundtrip = Array(@. gpu * 2.0f0 + 1.0f0)
expected = @. cpu * 2.0f0 + 1.0f0
max_error = maximum(abs.(roundtrip .- expected))

println("Metal smoke max_error=", max_error)
if max_error > 1.0f-5
    error("Metal smoke roundtrip exceeded tolerance")
end

println("Metal smoke OK")
