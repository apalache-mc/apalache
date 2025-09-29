#!/usr/bin/env python3
"""
Apalache Explorer Script

This script starts an Apalache server in explorer mode, loads a TLA+ specification,
explores transitions, and checks invariants. It terminates when an invariant is
violated or after exploring 100 transitions.

Usage:
    python explorer_script.py <spec_file> <invariant1> [invariant2] ...

Example:
    python explorer_script.py MySpec.tla TypeOK Safety
"""

import argparse
import json
import os
import random
import requests
import subprocess
import sys
import time
from pathlib import Path
from typing import List, Optional, Dict, Any


class ApalacheExplorer:
    def __init__(self, port: int = 8822):
        self.port = port
        self.base_url = f"http://localhost:{port}/rpc"
        self.server_process = None
        self.session_id = None
        self.current_snapshot_id = None
        self.current_step = 0
        self.transitions_explored = 0
        self.request_id_counter = 0

    def start_server(self) -> bool:
        """Start the Apalache server in explorer mode."""
        print("Starting Apalache server in explorer mode...")

        # Find the apalache-mc executable
        apalache_cmd = self._find_apalache_executable()
        if not apalache_cmd:
            print("Error: Could not find apalache-mc executable")
            return False

        # Start the server
        cmd = [apalache_cmd, "server", "--server-type", "explorer", "--port", str(self.port)]
        try:
            self.server_process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True
            )

            # Wait for server to start
            max_retries = 30
            for i in range(max_retries):
                try:
                    response = requests.get(f"http://localhost:{self.port}/rpc", timeout=1)
                    if response.status_code in [200, 405]:  # 405 is expected for GET on JSON-RPC endpoint
                        print(f"Server started successfully on port {self.port}")
                        return True
                except requests.exceptions.RequestException:
                    pass
                time.sleep(1)

            print("Error: Server failed to start within timeout")
            return False

        except Exception as e:
            print(f"Error starting server: {e}")
            return False

    def _find_apalache_executable(self) -> Optional[str]:
        """Find the apalache-mc executable."""
        # Check if it's in the bin directory of the project
        project_bin = Path(__file__).parent / "bin" / "apalache-mc"
        if project_bin.exists() and os.access(project_bin, os.X_OK):
            return str(project_bin)

        # Check PATH
        import shutil
        apalache_cmd = shutil.which("apalache-mc")
        if apalache_cmd:
            return apalache_cmd

        return None

    def stop_server(self):
        """Stop the Apalache server."""
        if self.server_process:
            print("Stopping Apalache server...")
            self.server_process.terminate()
            try:
                self.server_process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.server_process.kill()
                self.server_process.wait()
            self.server_process = None

    def _make_rpc_call(self, method: str, params: Dict[str, Any]) -> Dict[str, Any]:
        """Make a JSON-RPC call to the server."""
        self.request_id_counter += 1
        payload = {
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
            "id": self.request_id_counter
        }

        try:
            response = requests.post(
                self.base_url,
                json=payload,
                headers={"Content-Type": "application/json"},
                timeout=30
            )
            response.raise_for_status()
            return response.json()
        except Exception as e:
            print(f"Error making RPC call to {method}: {e}")
            raise

    def load_spec(self, spec_file: str, invariants: List[str]) -> bool:
        """Load a TLA+ specification."""
        print(f"Loading specification: {spec_file}")

        # Read the specification file
        try:
            with open(spec_file, 'r', encoding='utf-8') as f:
                spec_content = f.read()
        except Exception as e:
            print(f"Error reading specification file: {e}")
            return False

        # Make the loadSpec RPC call
        params = {
            "sources": [spec_content],
            "init": "Init",
            "next": "Next",
            "invariants": invariants
        }

        try:
            response = self._make_rpc_call("loadSpec", params)

            if "error" in response:
                print(f"Error loading specification: {response['error']}")
                return False

            result = response["result"]
            self.session_id = result["sessionId"]
            self.current_snapshot_id = result["snapshotId"]
            spec_params = result["specParameters"]

            print(f"Specification loaded successfully!")
            print(f"Session ID: {self.session_id}")
            print(f"Initial transitions: {spec_params['nInitTransitions']}")
            print(f"Next transitions: {spec_params['nNextTransitions']}")
            print(f"State invariants: {spec_params['nStateInvariants']}")
            print(f"Action invariants: {spec_params['nActionInvariants']}")

            return True

        except Exception as e:
            print(f"Error loading specification: {e}")
            return False

    def check_invariants(self, num_invariants: int) -> Optional[str]:
        """Check all invariants. Returns violated invariant name or None."""
        for inv_id in range(num_invariants):
            params = {
                "sessionId": self.session_id,
                "invariantId": inv_id,
                "timeoutSec": 10
            }

            try:
                response = self._make_rpc_call("checkInvariant", params)

                if "error" in response:
                    print(f"Error checking invariant {inv_id}: {response['error']}")
                    continue

                result = response["result"]
                status = result["invariantStatus"]

                if status == "VIOLATED":
                    print(f"\n*** INVARIANT VIOLATION DETECTED ***")
                    print(f"Invariant ID {inv_id} is violated!")
                    print(f"Counterexample:")
                    if result["trace"]:
                        print(json.dumps(result["trace"], indent=2))
                    return f"invariant_{inv_id}"
                elif status == "UNKNOWN":
                    print(f"Invariant {inv_id}: UNKNOWN (timeout or solver issue)")

            except Exception as e:
                print(f"Error checking invariant {inv_id}: {e}")

        return None

    def assume_transition(self, transition_id: int) -> bool:
        """Assume a transition and check if it's enabled."""
        params = {
            "sessionId": self.session_id,
            "snapshotId": self.current_snapshot_id,
            "transitionId": transition_id,
            "checkEnabled": True,
            "timeoutSec": 10
        }

        try:
            response = self._make_rpc_call("assumeTransition", params)

            if "error" in response:
                print(f"Error assuming transition {transition_id}: {response['error']}")
                return False

            result = response["result"]
            status = result["status"]
            self.current_snapshot_id = result["snapshotId"]

            if status == "ENABLED":
                print(f"Transition {transition_id}: ENABLED")
                return True
            elif status == "DISABLED":
                print(f"Transition {transition_id}: DISABLED")
                return False
            else:  # UNKNOWN
                print(f"Transition {transition_id}: UNKNOWN")
                return True  # Assume it's enabled for exploration

        except Exception as e:
            print(f"Error assuming transition {transition_id}: {e}")
            return False

    def next_step(self) -> bool:
        """Move to the next step."""
        params = {"sessionId": self.session_id}

        try:
            response = self._make_rpc_call("nextStep", params)

            if "error" in response:
                print(f"Error moving to next step: {response['error']}")
                return False

            result = response["result"]
            self.current_snapshot_id = result["snapshotId"]
            self.current_step = result["newStepNo"]

            print(f"Moved to step {self.current_step}")
            return True

        except Exception as e:
            print(f"Error moving to next step: {e}")
            return False

    def dispose_spec(self):
        """Dispose of the current specification session."""
        if self.session_id:
            params = {"sessionId": self.session_id}
            try:
                self._make_rpc_call("disposeSpec", params)
                print("Specification session disposed")
            except Exception as e:
                print(f"Error disposing specification: {e}")

    def explore(self, spec_file: str, invariants: List[str], max_transitions: int = 100):
        """Main exploration loop."""
        try:
            # Start server
            if not self.start_server():
                return False

            # Load specification
            if not self.load_spec(spec_file, invariants):
                return False

            print(f"\nStarting exploration (max {max_transitions} transitions)...")

            # Get initial spec parameters for transition counts
            # We'll assume we get this from the loadSpec response

            while self.transitions_explored < max_transitions:
                print(f"\n--- Transition {self.transitions_explored + 1} (Step {self.current_step}) ---")

                # Determine available transitions based on current step
                if self.current_step == 0:
                    # Use Init transitions - we'll try different transition IDs
                    max_transitions_to_try = 5  # Reasonable default
                else:
                    # Use Next transitions
                    max_transitions_to_try = 10  # Reasonable default

                # Try to find an enabled transition
                transition_found = False
                for trans_id in range(max_transitions_to_try):
                    if self.assume_transition(trans_id):
                        transition_found = True
                        break

                if not transition_found:
                    print("No enabled transitions found, exploration complete")
                    break

                # Move to next step
                if not self.next_step():
                    print("Failed to move to next step, stopping exploration")
                    break

                self.transitions_explored += 1

                # Check invariants after each transition
                num_invariants = len(invariants)
                violated_invariant = self.check_invariants(num_invariants)
                if violated_invariant:
                    print(f"\nExploration stopped due to invariant violation: {violated_invariant}")
                    break

                print(f"All invariants satisfied at step {self.current_step}")

            if self.transitions_explored >= max_transitions:
                print(f"\nExploration completed: reached maximum of {max_transitions} transitions")

            return True

        except KeyboardInterrupt:
            print("\nExploration interrupted by user")
            return False
        except Exception as e:
            print(f"Error during exploration: {e}")
            return False
        finally:
            # Clean up
            self.dispose_spec()
            self.stop_server()


def main():
    parser = argparse.ArgumentParser(
        description="Explore TLA+ specifications using Apalache",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python explorer_script.py MySpec.tla TypeOK
  python explorer_script.py MySpec.tla TypeOK Safety Liveness
        """
    )

    parser.add_argument("spec_file", help="TLA+ specification file")
    parser.add_argument("invariants", nargs="+", help="Names of invariants to check")
    parser.add_argument("--port", type=int, default=8822, help="Server port (default: 8822)")
    parser.add_argument("--max-transitions", type=int, default=100,
                       help="Maximum number of transitions to explore (default: 100)")

    args = parser.parse_args()

    # Validate spec file exists
    if not os.path.exists(args.spec_file):
        print(f"Error: Specification file '{args.spec_file}' not found")
        return 1

    # Create explorer and run
    explorer = ApalacheExplorer(port=args.port)
    success = explorer.explore(args.spec_file, args.invariants, args.max_transitions)

    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
