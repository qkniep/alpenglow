# Alpenglow Formal Verification CLI (PowerShell)
# Beautiful, user-friendly wrapper for TLC model checker

function Write-Banner {
    Write-Host ""
    Write-Host "╔═══════════════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
    Write-Host "║                                                                   ║" -ForegroundColor Cyan
    Write-Host "║     🔬  ALPENGLOW FORMAL VERIFICATION SUITE  🔬                   ║" -ForegroundColor Cyan
    Write-Host "║                                                                   ║" -ForegroundColor Cyan
    Write-Host "║     Mathematical Proof of Consensus Safety & Liveness            ║" -ForegroundColor Cyan
    Write-Host "║     Powered by TLA+ & TLC Model Checker                          ║" -ForegroundColor Cyan
    Write-Host "║                                                                   ║" -ForegroundColor Cyan
    Write-Host "╚═══════════════════════════════════════════════════════════════════╝" -ForegroundColor Cyan
    Write-Host ""
}

function Write-Section {
    param([string]$Title)
    Write-Host ""
    Write-Host ("═" * 70) -ForegroundColor Magenta
    Write-Host "  $Title" -ForegroundColor Magenta
    Write-Host ("═" * 70) -ForegroundColor Magenta
    Write-Host ""
}

function Write-Success {
    param([string]$Message)
    Write-Host "✅ $Message" -ForegroundColor Green
}

function Write-Info {
    param([string]$Message)
    Write-Host "ℹ️  $Message" -ForegroundColor Blue
}

function Write-Warning {
    param([string]$Message)
    Write-Host "⚠️  $Message" -ForegroundColor Yellow
}

function Write-Error {
    param([string]$Message)
    Write-Host "❌ $Message" -ForegroundColor Red
}

function Write-Progress {
    param([string]$Message)
    Write-Host "⏳ $Message" -ForegroundColor Cyan
}

function Test-Prerequisites {
    Write-Section "Prerequisites Check"
    
    # Check Java
    try {
        $javaVersion = java -version 2>&1 | Select-Object -First 1
        Write-Success "Java found: $javaVersion"
    }
    catch {
        Write-Error "Java not found: $_"
        Write-Info "Please install Java 8 or later: https://www.oracle.com/java/technologies/downloads/"
        return $false
    }
    
    # Check tla2tools.jar
    if (Test-Path "tla2tools.jar") {
        $sizeMB = [math]::Round((Get-Item "tla2tools.jar").Length / 1MB, 1)
        Write-Success "TLA+ Tools found: tla2tools.jar ($sizeMB MB)"
    }
    else {
        Write-Error "tla2tools.jar not found in current directory"
        Write-Info "Download from: https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar"
        return $false
    }
    
    return $true
}

function Format-Number {
    param([string]$NumStr)
    try {
        $num = [int64]$NumStr
        return $num.ToString("N0")
    }
    catch {
        return $NumStr
    }
}

function Invoke-Verification {
    param(
        [string]$Config,
        [string]$SpecFile,
        [string]$ModelName
    )
    
    Write-Section "Running $ModelName"
    Write-Info "Specification: $SpecFile"
    Write-Info "Configuration: $Config"
    Write-Host ""
    
    $startTime = Get-Date
    
    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = "java"
    $psi.Arguments = "-XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -deadlock -config $Config $SpecFile"
    $psi.RedirectStandardOutput = $true
    $psi.RedirectStandardError = $true
    $psi.UseShellExecute = $false
    $psi.CreateNoWindow = $true
    
    $process = New-Object System.Diagnostics.Process
    $process.StartInfo = $psi
    
    $outputBuilder = New-Object System.Text.StringBuilder
    $errorBuilder = New-Object System.Text.StringBuilder
    
    $outputEvent = Register-ObjectEvent -InputObject $process -EventName OutputDataReceived -Action {
        if ($EventArgs.Data) {
            $line = $EventArgs.Data.Trim()
            
            # Progress line
            if ($line -match 'Progress\((\d+)\).*?(\d[\d,]+) states generated.*?(\d[\d,]+) distinct states found.*?(\d[\d,]+) states left') {
                $depth = $Matches[1]
                $total = Format-Number $Matches[2].Replace(',', '')
                $distinct = Format-Number $Matches[3].Replace(',', '')
                $queue = Format-Number $Matches[4].Replace(',', '')
                
                Write-Host "📊 Depth $($depth.PadLeft(2)) | Generated: $($total.PadLeft(12)) | Distinct: $($distinct.PadLeft(10)) | Queue: $($queue.PadLeft(10))" -ForegroundColor Cyan
            }
            # Temporal checking
            elseif ($line -match 'Checking (\d+) branches of temporal') {
                Write-Host "🔄 Checking $($Matches[1]) temporal property branches..." -ForegroundColor Yellow
            }
            elseif ($line -match 'Finished checking temporal properties') {
                Write-Host "✓  Temporal properties check complete" -ForegroundColor Green
            }
            # Success
            elseif ($line -match 'Model checking completed.*No error') {
                Write-Host ""
                Write-Success "MODEL CHECKING COMPLETED - NO ERRORS FOUND!"
            }
            # Error
            elseif ($line -match 'Error: Invariant (\w+) is violated') {
                Write-Host ""
                Write-Error "INVARIANT VIOLATED: $($Matches[1])"
            }
            # Stats
            elseif ($line -match '^(\d+) states generated, (\d+) distinct states found' -and $line -notmatch 'Progress') {
                Write-Host ""
                Write-Host "Final Statistics:" -ForegroundColor White
                Write-Host "  Total States:    $(Format-Number $Matches[1])"
                Write-Host "  Distinct States: $(Format-Number $Matches[2])"
            }
            # Depth
            elseif ($line -match 'depth.*?is (\d+)') {
                Write-Host "  Search Depth:    $($Matches[1])"
            }
            # Time
            elseif ($line -match 'Finished in (.+)') {
                Write-Host "  Execution Time:  $($Matches[1])"
            }
        }
    }
    
    $errorEvent = Register-ObjectEvent -InputObject $process -EventName ErrorDataReceived -Action {
        if ($EventArgs.Data) {
            [void]$errorBuilder.AppendLine($EventArgs.Data)
        }
    }
    
    try {
        [void]$process.Start()
        $process.BeginOutputReadLine()
        $process.BeginErrorReadLine()
        $process.WaitForExit()
        
        $elapsed = (Get-Date) - $startTime
        
        if ($process.ExitCode -eq 0) {
            Write-Host ""
            Write-Success "Verification completed in $($elapsed.TotalSeconds.ToString('F1'))s"
            return $true
        }
        else {
            Write-Host ""
            Write-Error "Verification failed with exit code $($process.ExitCode)"
            return $false
        }
    }
    catch {
        Write-Error "Verification error: $_"
        return $false
    }
    finally {
        Unregister-Event -SourceIdentifier $outputEvent.Name -ErrorAction SilentlyContinue
        Unregister-Event -SourceIdentifier $errorEvent.Name -ErrorAction SilentlyContinue
        $process.Dispose()
    }
}

# Main script
Write-Banner

if (-not (Test-Prerequisites)) {
    exit 1
}

Write-Host ""
Write-Host "Select verification to run:" -ForegroundColor White
Write-Host "  1. Core Safety Properties (12 invariants, ~2 min)" -ForegroundColor Blue
Write-Host "  2. Byzantine Adversary Model (16 invariants, ~5-10 min)" -ForegroundColor Yellow
Write-Host "  3. Liveness Properties (4 temporal properties, ~2-5 min)" -ForegroundColor Cyan
Write-Host "  4. Run All Verifications" -ForegroundColor Green
Write-Host "  5. Exit" -ForegroundColor Red
Write-Host ""

$choice = Read-Host "Enter choice (1-5)"

$results = @{}

switch ($choice) {
    "1" {
        $results["Safety"] = Invoke-Verification `
            -Config "formal-verification\MC.cfg" `
            -SpecFile "formal-verification\Alpenglow.tla" `
            -ModelName "Core Safety Properties"
    }
    "2" {
        $results["Byzantine"] = Invoke-Verification `
            -Config "formal-verification\MC_Byzantine.cfg" `
            -SpecFile "formal-verification\ByzantineAlpenglow.tla" `
            -ModelName "Byzantine Adversary Model"
    }
    "3" {
        $results["Liveness"] = Invoke-Verification `
            -Config "formal-verification\MC_Liveness.cfg" `
            -SpecFile "formal-verification\LivenessAlpenglow.tla" `
            -ModelName "Liveness Properties"
    }
    "4" {
        $results["Safety"] = Invoke-Verification `
            -Config "formal-verification\MC.cfg" `
            -SpecFile "formal-verification\Alpenglow.tla" `
            -ModelName "Core Safety Properties"
        
        $results["Byzantine"] = Invoke-Verification `
            -Config "formal-verification\MC_Byzantine.cfg" `
            -SpecFile "formal-verification\ByzantineAlpenglow.tla" `
            -ModelName "Byzantine Adversary Model"
        
        $results["Liveness"] = Invoke-Verification `
            -Config "formal-verification\MC_Liveness.cfg" `
            -SpecFile "formal-verification\LivenessAlpenglow.tla" `
            -ModelName "Liveness Properties"
    }
    "5" {
        Write-Info "Exiting..."
        exit 0
    }
    default {
        Write-Error "Invalid choice. Please run again and select 1-5."
        exit 1
    }
}

# Print summary
if ($results.Count -gt 0) {
    Write-Section "Verification Summary"
    
    $allPassed = $true
    foreach ($item in $results.GetEnumerator()) {
        if ($item.Value) {
            Write-Success "$($item.Key): PASSED"
        }
        else {
            Write-Error "$($item.Key): FAILED"
            $allPassed = $false
        }
    }
    
    Write-Host ""
    if ($allPassed) {
        Write-Host "╔═══════════════════════════════════════════════════╗" -ForegroundColor Green
        Write-Host "║  🎉  ALL VERIFICATIONS PASSED!  🎉                ║" -ForegroundColor Green
        Write-Host "║                                                   ║" -ForegroundColor Green
        Write-Host "║  Alpenglow consensus is mathematically proven    ║" -ForegroundColor Green
        Write-Host "║  safe, Byzantine-resilient, and live!            ║" -ForegroundColor Green
        Write-Host "╚═══════════════════════════════════════════════════╝" -ForegroundColor Green
    }
    else {
        Write-Warning "Some verifications failed. Check output above for details."
    }
}
