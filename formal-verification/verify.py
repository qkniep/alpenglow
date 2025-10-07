#!/usr/bin/env python3
"""
Alpenglow Formal Verification CLI
Beautiful, user-friendly wrapper for TLC model checker
"""

import subprocess
import sys
import os
import time
import re
from datetime import datetime
from typing import Optional, Dict, List, Tuple

# Global variable for jar path (set by check_prerequisites)
TLA_JAR_PATH = None

# Fix Windows console encoding for Unicode characters
if sys.platform == 'win32':
    try:
        import codecs
        sys.stdout = codecs.getwriter('utf-8')(sys.stdout.buffer, 'strict')
        sys.stderr = codecs.getwriter('utf-8')(sys.stderr.buffer, 'strict')
    except:
        pass  # Fallback to default if encoding setup fails

# Emoji support - use simple chars on Windows if Unicode fails
USE_EMOJI = True
try:
    test = "🔬"
    print(test, end='', file=open(os.devnull, 'w'))
except:
    USE_EMOJI = False

# Box drawing character support - use ASCII on Windows if Unicode fails
USE_BOX_CHARS = True
try:
    test = "╔═╗"
    print(test, end='', file=open(os.devnull, 'w'))
except:
    USE_BOX_CHARS = False

def emoji(unicode_char: str, fallback: str) -> str:
    """Return emoji or fallback based on terminal support"""
    return unicode_char if USE_EMOJI else fallback

def box_char(unicode_char: str, fallback: str) -> str:
    """Return box drawing char or fallback based on terminal support"""
    return unicode_char if USE_BOX_CHARS else fallback

# ANSI color codes
class Colors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def print_banner():
    """Print beautiful ASCII banner"""
    banner = f"""
{Colors.BOLD}{Colors.OKCYAN}
{box_char('╔════════════════════════════════════════════════════════════════════╗', '================================================================================')}
{box_char('║                                                                    ║', '|                                                                            |')}
{box_char('║        ', '        ')}{emoji('🔬', '*')} ALPENGLOW FORMAL VERIFICATION SUITE {emoji('🔬', '*')}{box_char('              ║', '              |')}
{box_char('║                                                                    ║', '|                                                                            |')}
{box_char('║        Mathematical Proof of Consensus Safety & Liveness          ║', '|        Mathematical Proof of Consensus Safety & Liveness          |')}
{box_char('║        Powered by TLA+ & TLC Model Checker                        ║', '|        Powered by TLA+ & TLC Model Checker                        |')}
{box_char('║                                                                    ║', '|                                                                            |')}
{box_char('╚════════════════════════════════════════════════════════════════════╝', '================================================================================')}{Colors.ENDC}
"""
    print(banner)

def print_section(title: str):
    """Print section header"""
    print(f"\n{Colors.BOLD}{Colors.HEADER}{box_char('╔', '+')}{'═' * 68}{box_char('╗', '+')}{Colors.ENDC}")
    print(f"{Colors.BOLD}{Colors.HEADER}{box_char('║', '|')}  {title:<64}  {box_char('║', '|')}{Colors.ENDC}")
    print(f"{Colors.BOLD}{Colors.HEADER}{box_char('╚', '+')}{'═' * 68}{box_char('╝', '+')}{Colors.ENDC}\n")

def print_success(message: str):
    """Print success message"""
    print(f"{Colors.OKGREEN}{Colors.BOLD}  {emoji('✅', '[✓]')} {message}{Colors.ENDC}")

def print_info(message: str):
    """Print info message"""
    print(f"{Colors.OKBLUE}  {emoji('ℹ️', '[i]')} {message}{Colors.ENDC}")

def print_warning(message: str):
    """Print warning message"""
    print(f"{Colors.WARNING}{Colors.BOLD}  {emoji('⚠️', '[!]')} {message}{Colors.ENDC}")

def print_error(message: str):
    """Print error message"""
    print(f"{Colors.FAIL}{Colors.BOLD}  {emoji('❌', '[✗]')} {message}{Colors.ENDC}")

def print_progress(message: str):
    """Print progress message"""
    print(f"{Colors.OKCYAN}  {emoji('⏳', '[...]')} {message}{Colors.ENDC}")

def check_prerequisites() -> bool:
    """Check if Java and tla2tools.jar are available"""
    global TLA_JAR_PATH
    
    print_section("Prerequisites Check")
    
    # Check Java
    try:
        result = subprocess.run(['java', '-version'], 
                              capture_output=True, text=True, timeout=5)
        java_version = result.stderr.split('\n')[0]
        print_success(f"Java found: {java_version}")
    except Exception as e:
        print_error(f"Java not found: {e}")
        print_info("Please install Java 8 or later: https://www.oracle.com/java/technologies/downloads/")
        return False
    
    # Check tla2tools.jar (look in current dir and parent dir)
    jar_paths = ['tla2tools.jar', '../tla2tools.jar', 
                 os.path.join('..', 'tla2tools.jar')]
    jar_path = None
    for path in jar_paths:
        if os.path.exists(path):
            jar_path = path
            break
    
    if jar_path:
        TLA_JAR_PATH = jar_path  # Store for later use
        size_mb = os.path.getsize(jar_path) / (1024 * 1024)
        print_success(f"TLA+ Tools found: {jar_path} ({size_mb:.1f} MB)")
    else:
        print_error("tla2tools.jar not found in current or parent directory")
        print_info("Download from: https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar")
        return False
    
    return True

def parse_tlc_output(line: str) -> Optional[Dict]:
    """Parse TLC output line and extract meaningful info"""
    
    # Progress line: "Progress(10) at 2025-10-06 12:43:37: 123,270 states generated..."
    progress_match = re.search(r'Progress\((\d+)\).*?(\d[\d,]+) states generated.*?(\d[\d,]+) distinct states found.*?(\d[\d,]+) states left', line)
    if progress_match:
        return {
            'type': 'progress',
            'depth': int(progress_match.group(1)),
            'total': progress_match.group(2).replace(',', ''),
            'distinct': progress_match.group(3).replace(',', ''),
            'queue': progress_match.group(4).replace(',', '')
        }
    
    # Completion: "Model checking completed. No error has been found."
    if 'Model checking completed' in line and 'No error' in line:
        return {'type': 'success'}
    
    # Error: "Error: Invariant <name> is violated"
    if 'Error: Invariant' in line and 'violated' in line:
        inv_match = re.search(r'Invariant (\w+) is violated', line)
        return {'type': 'error', 'invariant': inv_match.group(1) if inv_match else 'Unknown'}
    
    # Final stats: "6229333 states generated, 839515 distinct states found"
    stats_match = re.search(r'(\d+) states generated, (\d+) distinct states found', line)
    if stats_match and 'Progress' not in line:
        return {
            'type': 'stats',
            'total': stats_match.group(1),
            'distinct': stats_match.group(2)
        }
    
    # Depth: "The depth of the complete state graph search is"
    depth_match = re.search(r'depth.*?is (\d+)', line)
    if depth_match:
        return {'type': 'depth', 'value': depth_match.group(1)}
    
    # Time: "Finished in 01min 26s"
    time_match = re.search(r'Finished in (.+)', line)
    if time_match:
        return {'type': 'time', 'value': time_match.group(1)}
    
    # Temporal checking: "Checking 4 branches of temporal properties"
    temporal_match = re.search(r'Checking (\d+) branches of temporal', line)
    if temporal_match:
        return {'type': 'temporal_start', 'branches': temporal_match.group(1)}
    
    if 'Finished checking temporal properties' in line:
        return {'type': 'temporal_done'}
    
    return None

def format_number(num_str: str) -> str:
    """Format number with commas"""
    try:
        num = int(num_str)
        return f"{num:,}"
    except:
        return num_str

def run_verification(model: str, config: str, spec_file: str, model_name: str) -> bool:
    """Run TLC verification with beautiful output"""
    global TLA_JAR_PATH
    
    print_section(f"Running {model_name}")
    print_info(f"Specification: {spec_file}")
    print_info(f"Configuration: {config}")
    print()
    
    cmd = [
        'java', '-XX:+UseParallelGC', '-cp', TLA_JAR_PATH,
        'tlc2.TLC', '-deadlock',
        '-config', config,
        spec_file
    ]
    
    start_time = time.time()
    last_progress_time = start_time
    
    try:
        process = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
            universal_newlines=True
        )
        
        last_stats = {}
        temporal_checking = False
        
        for line in process.stdout: # type: ignore
            line = line.strip()
            if not line:
                continue
            
            parsed = parse_tlc_output(line)
            
            if parsed:
                if parsed['type'] == 'progress':
                    elapsed = time.time() - last_progress_time
                    total = format_number(parsed['total'])
                    distinct = format_number(parsed['distinct'])
                    queue = format_number(parsed['queue'])
                    depth = parsed['depth']
                    
                    print(f"{Colors.OKCYAN}  {emoji('📊', '►')} Depth {depth:2} │ "
                          f"States: {total:>12} │ "
                          f"Distinct: {distinct:>10} │ "
                          f"Queue: {queue:>10}{Colors.ENDC}")
                    
                    last_progress_time = time.time()
                    last_stats = parsed
                
                elif parsed['type'] == 'temporal_start':
                    temporal_checking = True
                    print(f"\n{Colors.WARNING}  {emoji('🔄', '⟳')} Checking {parsed['branches']} temporal property branches...{Colors.ENDC}")
                
                elif parsed['type'] == 'temporal_done':
                    if temporal_checking:
                        print(f"{Colors.OKGREEN}  {emoji('✓', '✓')} Temporal properties verified{Colors.ENDC}\n")
                        temporal_checking = False
                
                elif parsed['type'] == 'success':
                    print()
                    print(f"{Colors.BOLD}{Colors.OKGREEN}{'─' * 70}{Colors.ENDC}")
                    print_success("MODEL CHECKING COMPLETED - NO ERRORS FOUND!")
                    print(f"{Colors.BOLD}{Colors.OKGREEN}{'─' * 70}{Colors.ENDC}")
                
                elif parsed['type'] == 'error':
                    print()
                    print_error(f"INVARIANT VIOLATED: {parsed['invariant']}")
                    return False
                
                elif parsed['type'] == 'stats':
                    total = format_number(parsed['total'])
                    distinct = format_number(parsed['distinct'])
                    print(f"\n{Colors.BOLD}{Colors.OKCYAN}┌─ Final Statistics {'─' * 46}┐{Colors.ENDC}")
                    print(f"{Colors.OKCYAN}│  Total States:    {total:>12}                              │{Colors.ENDC}")
                    print(f"{Colors.OKCYAN}│  Distinct States: {distinct:>12}                              │{Colors.ENDC}")
                
                elif parsed['type'] == 'depth':
                    print(f"{Colors.OKCYAN}│  Search Depth:    {parsed['value']:>12}                              │{Colors.ENDC}")
                
                elif parsed['type'] == 'time':
                    print(f"{Colors.OKCYAN}│  Execution Time:  {parsed['value']:>12}                              │{Colors.ENDC}")
                    print(f"{Colors.BOLD}{Colors.OKCYAN}└{'─' * 68}┘{Colors.ENDC}")
        
        process.wait()
        
        if process.returncode == 0:
            elapsed = time.time() - start_time
            print()
            print_success(f"Verification completed in {elapsed:.1f}s")
            return True
        else:
            print()
            print_error(f"Verification failed with exit code {process.returncode}")
            return False
            
    except KeyboardInterrupt:
        print()
        print_warning("Verification interrupted by user")
        process.kill() # type: ignore
        return False
    except Exception as e:
        print_error(f"Verification error: {e}")
        return False

def show_menu():
    """Display the main menu"""
    print()
    print(f"{Colors.BOLD}{Colors.HEADER}{box_char('╔════════════════════════════════════════════════════════════════════╗', '================================================================================')}{Colors.ENDC}")
    print(f"{Colors.BOLD}{Colors.HEADER}{box_char('║  Select Verification to Run:                                      ║', '|  Select Verification to Run:                                      |')}{Colors.ENDC}")
    print(f"{Colors.BOLD}{Colors.HEADER}{box_char('╚════════════════════════════════════════════════════════════════════╝', '================================================================================')}{Colors.ENDC}")
    print()
    print(f"  {Colors.OKBLUE}{Colors.BOLD}[1]{Colors.ENDC} {Colors.OKBLUE}Core Safety Properties{Colors.ENDC}")
    print(f"      {Colors.ENDC}→ 12 invariants, ~2 minutes{Colors.ENDC}")
    print()
    print(f"  {Colors.WARNING}{Colors.BOLD}[2]{Colors.ENDC} {Colors.WARNING}Byzantine Adversary Model{Colors.ENDC}")
    print(f"      {Colors.ENDC}→ 16 invariants, ~5-10 minutes{Colors.ENDC}")
    print()
    print(f"  {Colors.OKCYAN}{Colors.BOLD}[3]{Colors.ENDC} {Colors.OKCYAN}Liveness Properties{Colors.ENDC}")
    print(f"      {Colors.ENDC}→ 4 temporal properties, ~2-5 minutes{Colors.ENDC}")
    print()
    print(f"  {Colors.OKGREEN}{Colors.BOLD}[4]{Colors.ENDC} {Colors.OKGREEN}Run All Verifications{Colors.ENDC}")
    print(f"      {Colors.ENDC}→ Complete verification suite{Colors.ENDC}")
    print()
    print(f"  {Colors.OKCYAN}{Colors.BOLD}[5]{Colors.ENDC} {Colors.OKCYAN}View Results Summary{Colors.ENDC}")
    print(f"      {Colors.ENDC}→ Show all completed verifications{Colors.ENDC}")
    print()
    print(f"  {Colors.WARNING}{Colors.BOLD}[6]{Colors.ENDC} {Colors.WARNING}Rotor Block Propagation{Colors.ENDC}")
    print(f"      {Colors.ENDC}→ 3 invariants, ~1-2 minutes{Colors.ENDC}")
    print()
    print(f"  {Colors.OKCYAN}{Colors.BOLD}[7]{Colors.ENDC} {Colors.OKCYAN}20+20 Resilience Proof{Colors.ENDC}")
    print(f"      {Colors.ENDC}→ 11 invariants, ~3-5 minutes{Colors.ENDC}")
    print()
    print(f"  {Colors.WARNING}{Colors.BOLD}[8]{Colors.ENDC} {Colors.WARNING}Large-Scale Simulation{Colors.ENDC}")
    print(f"      {Colors.ENDC}→ 20 validators, statistical verification{Colors.ENDC}")
    print()
    print(f"  {Colors.FAIL}{Colors.BOLD}[0]{Colors.ENDC} Exit")
    print()

def print_summary(all_results: Dict[str, bool]):
    """Print summary of all verifications"""
    if not all_results:
        print_warning("No verifications have been run yet.")
        return
    
    print_section("Verification Summary")
    all_passed = True
    for name, passed in all_results.items():
        if passed:
            print(f"  {Colors.OKGREEN}{Colors.BOLD}{emoji('✅', '[✓]')} {name:<20} PASSED{Colors.ENDC}")
        else:
            print(f"  {Colors.FAIL}{Colors.BOLD}{emoji('❌', '[✗]')} {name:<20} FAILED{Colors.ENDC}")
            all_passed = False
    
    print()
    if all_passed:
        print(f"{Colors.BOLD}{Colors.OKGREEN}")
        print(f"{box_char('╔════════════════════════════════════════════════════════════════════╗', '================================================================================')}")
        print(f"{box_char('║                                                                    ║', '|                                                                            |')}")
        print(f"{box_char('║      ', '      ')}{emoji('🎉', '***')} ALL VERIFICATIONS PASSED! {emoji('🎉', '***')}{box_char('                          ║', '                          |')}")
        print(f"{box_char('║                                                                    ║', '|                                                                            |')}")
        print(f"{box_char('║      Alpenglow consensus is mathematically proven                 ║', '|      Alpenglow consensus is mathematically proven                 |')}")
        print(f"{box_char('║      safe, Byzantine-resilient, and live!                         ║', '|      safe, Byzantine-resilient, and live!                         |')}")
        print(f"{box_char('║                                                                    ║', '|                                                                            |')}")
        print(f"{box_char('╚════════════════════════════════════════════════════════════════════╝', '================================================================================')}")
        print(f"{Colors.ENDC}")
    else:
        print_warning("Some verifications failed. Check output above for details.")

def main():
    """Main CLI entry point"""
    print_banner()
    
    # Check prerequisites
    if not check_prerequisites():
        sys.exit(1)
    
    # Track all results across multiple runs
    all_results = {}
    
    # Main menu loop
    while True:
        show_menu()
        
        choice = input(f"{Colors.BOLD}Enter choice (0-8): {Colors.ENDC}").strip()
        
        if choice == '0':
            print()
            print_info("Exiting verification suite...")
            if all_results:
                print()
                print_summary(all_results)
            print()
            print(f"{Colors.BOLD}{Colors.OKCYAN}Thank you for using Alpenglow Formal Verification!{Colors.ENDC}")
            print()
            break
        
        elif choice == '5':
            print_summary(all_results)
            input(f"\n{Colors.BOLD}Press Enter to continue...{Colors.ENDC}")
            continue
        
        elif choice == '6':
            success = run_verification(
                'rotor',
                'RotorMC.cfg',
                'Rotor.tla',
                'Rotor Block Propagation'
            )
            all_results['Rotor Propagation'] = success
        
        elif choice == '7':
            success = run_verification(
                'resilience',
                'ResilienceAlpenglowMC.cfg',
                'ResilienceAlpenglow.tla',
                '20+20 Resilience Proof'
            )
            all_results['20+20 Resilience'] = success
        
        elif choice == '8':
            success = run_verification(
                'simulation',
                'AlpenglowSimulation.cfg',
                'AlpenglowSimulation.tla',
                'Large-Scale Simulation'
            )
            all_results['Large-Scale Simulation'] = success
        
        elif choice not in ['1', '2', '3', '4']:
            print_error("Invalid choice. Please enter 0-8.")
            input(f"\n{Colors.BOLD}Press Enter to continue...{Colors.ENDC}")
            continue
        
        # Run selected verifications
        if choice == '1':
            success = run_verification(
                'safety',
                'MC.cfg',
                'Alpenglow.tla',
                'Core Safety Properties'
            )
            all_results['Core Safety'] = success
        
        elif choice == '2':
            success = run_verification(
                'byzantine',
                'MC_Byzantine.cfg',
                'ByzantineAlpenglow.tla',
                'Byzantine Adversary Model'
            )
            all_results['Byzantine Resilience'] = success
        
        elif choice == '3':
            success = run_verification(
                'liveness',
                'MC_Liveness.cfg',
                'LivenessAlpenglow.tla',
                'Liveness Properties'
            )
            all_results['Liveness'] = success
        
        elif choice == '4':
            # Run all verifications
            success1 = run_verification(
                'safety',
                'MC.cfg',
                'Alpenglow.tla',
                'Core Safety Properties'
            )
            all_results['Core Safety'] = success1
            
            success2 = run_verification(
                'byzantine',
                'MC_Byzantine.cfg',
                'ByzantineAlpenglow.tla',
                'Byzantine Adversary Model'
            )
            all_results['Byzantine Resilience'] = success2
            
            success3 = run_verification(
                'liveness',
                'MC_Liveness.cfg',
                'LivenessAlpenglow.tla',
                'Liveness Properties'
            )
            all_results['Liveness'] = success3
            
            success4 = run_verification(
                'rotor',
                'RotorMC.cfg',
                'Rotor.tla',
                'Rotor Block Propagation'
            )
            all_results['Rotor Propagation'] = success4
            
            success5 = run_verification(
                'resilience',
                'ResilienceAlpenglowMC.cfg',
                'ResilienceAlpenglow.tla',
                '20+20 Resilience Proof'
            )
            all_results['20+20 Resilience'] = success5
            
            success6 = run_verification(
                'simulation',
                'AlpenglowSimulation.cfg',
                'AlpenglowSimulation.tla',
                'Large-Scale Simulation'
            )
            all_results['Large-Scale Simulation'] = success6
        
        # Show quick summary after each run
        print()
        print(f"{Colors.BOLD}{'─' * 70}{Colors.ENDC}")
        print(f"{Colors.BOLD}Quick Summary:{Colors.ENDC}")
        for name, passed in all_results.items():
            status = f"{Colors.OKGREEN}PASSED{Colors.ENDC}" if passed else f"{Colors.FAIL}FAILED{Colors.ENDC}"
            print(f"  {name}: {status}")
        print(f"{Colors.BOLD}{'─' * 70}{Colors.ENDC}")
        print()
        
        input(f"{Colors.BOLD}Press Enter to return to menu...{Colors.ENDC}")

if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        print()
        print_info("Interrupted by user. Goodbye!")
        sys.exit(0)
