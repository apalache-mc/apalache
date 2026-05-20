// Populate the sidebar
//
// This is a script, and not included directly in the page, to control the total size of the book.
// The TOC contains an entry for each page, so if each page includes a copy of the TOC,
// the total size of the page becomes O(n**2).
class MDBookSidebarScrollbox extends HTMLElement {
    constructor() {
        super();
    }
    connectedCallback() {
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="index.html">Overview</a></span></li><li class="chapter-item expanded "><li class="part-title">Tutorials</li></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="tutorials/index.html"><strong aria-hidden="true">1.</strong> Overview</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="tutorials/entry-tutorial.html"><strong aria-hidden="true">2.</strong> Entry-level Model Checker Tutorial</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="tutorials/snowcat-tutorial.html"><strong aria-hidden="true">3.</strong> Type Checker Tutorial</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="tutorials/pluscal-tutorial.html"><strong aria-hidden="true">4.</strong> Checking Pluscal specifications</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="tutorials/trail-tips.html"><strong aria-hidden="true">5.</strong> Apalache trail tips: how to check your specs faster</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="tutorials/symbmc.html"><strong aria-hidden="true">6.</strong> Symbolic Model Checking</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="tutorials/temporal-properties.html"><strong aria-hidden="true">7.</strong> Specifying temporal properties and understanding counterexamples</a></span></li><li class="chapter-item expanded "><li class="part-title">HOWTOs</li></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="HOWTOs/index.html"><strong aria-hidden="true">8.</strong> Overview</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="HOWTOs/howto-write-type-annotations.html"><strong aria-hidden="true">9.</strong> How to write type annotations</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="HOWTOs/uninterpretedTypes.html"><strong aria-hidden="true">10.</strong> How to use uninterpreted types</a></span></li><li class="chapter-item expanded "><li class="part-title">Apalache User Manual</li></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/index.html"><strong aria-hidden="true">11.</strong> Getting Started</a></span><ol class="section"><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/installation/index.html"><strong aria-hidden="true">11.1.</strong> Installation</a></span><ol class="section"><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/installation/jvm.html"><strong aria-hidden="true">11.1.1.</strong> Prebuilt Packages</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/installation/docker.html"><strong aria-hidden="true">11.1.2.</strong> Docker</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/installation/source.html"><strong aria-hidden="true">11.1.3.</strong> Build from Source</a></span></li></ol><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/running.html"><strong aria-hidden="true">11.2.</strong> Running the Tool</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/example.html"><strong aria-hidden="true">11.3.</strong> An Example TLA+ Specification</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/parameters.html"><strong aria-hidden="true">11.4.</strong> Specification Parameters</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/principles/index.html"><strong aria-hidden="true">11.5.</strong> Symbolic Model Checking with Apalache</a></span><ol class="section"><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/principles/assignments.html"><strong aria-hidden="true">11.5.1.</strong> Assignments and symbolic transitions</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/principles/folds.html"><strong aria-hidden="true">11.5.2.</strong> Folding sets and sequences</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/principles/invariants.html"><strong aria-hidden="true">11.5.3.</strong> Invariants: State, Action, Trace</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/principles/enumeration.html"><strong aria-hidden="true">11.5.4.</strong> Enumeration of counterexamples</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/principles/apalache-mod.html"><strong aria-hidden="true">11.5.5.</strong> The Apalache Module</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/principles/naturals.html"><strong aria-hidden="true">11.5.6.</strong> Naturals</a></span></li></ol><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/config.html"><strong aria-hidden="true">11.6.</strong> Apalache global configuration file</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/statistics.html"><strong aria-hidden="true">11.7.</strong> TLA+ Execution Statistics</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/profiling.html"><strong aria-hidden="true">11.8.</strong> Profiling Your Specification</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/theory.html"><strong aria-hidden="true">11.9.</strong> Five minutes of theory</a></span></li></ol><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/tuning.html"><strong aria-hidden="true">12.</strong> Fine Tuning</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/tlc-config.html"><strong aria-hidden="true">13.</strong> TLC Configuration Files</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/typechecker-snowcat.html"><strong aria-hidden="true">14.</strong> The Snowcat Type Checker</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/features.html"><strong aria-hidden="true">15.</strong> Supported Features</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/principles/recursive.html"><strong aria-hidden="true">16.</strong> Obsolete: Recursive operators and functions</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/known-issues.html"><strong aria-hidden="true">17.</strong> Known Issues</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/antipatterns.html"><strong aria-hidden="true">18.</strong> Antipatterns</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/preprocessing.html"><strong aria-hidden="true">19.</strong> TLA+ Preprocessing</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/assignments-in-depth.html"><strong aria-hidden="true">20.</strong> Assignments and Symbolic Transitions in Depth</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="apalache/kera.html"><strong aria-hidden="true">21.</strong> KerA: kernel logic of actions</a></span></li><li class="chapter-item expanded "><li class="part-title">TLA+ Language Manual for Engineers</li></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/index.html"><strong aria-hidden="true">22.</strong> Introduction</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/standard-operators.html"><strong aria-hidden="true">23.</strong> The standard operators of TLA+</a></span><ol class="section"><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/booleans.html"><strong aria-hidden="true">23.1.</strong> Booleans</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/control-and-nondeterminism.html"><strong aria-hidden="true">23.2.</strong> Control And Nondeterminism</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/conditionals.html"><strong aria-hidden="true">23.3.</strong> Conditionals</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/integers.html"><strong aria-hidden="true">23.4.</strong> Integers</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/sets.html"><strong aria-hidden="true">23.5.</strong> Sets</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/logic.html"><strong aria-hidden="true">23.6.</strong> Logic</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/functions.html"><strong aria-hidden="true">23.7.</strong> Functions</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/records.html"><strong aria-hidden="true">23.8.</strong> Records</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/tuples.html"><strong aria-hidden="true">23.9.</strong> Tuples</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/sequences.html"><strong aria-hidden="true">23.10.</strong> Sequences</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><span><strong aria-hidden="true">23.11.</strong> Bags</span></span></li></ol><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/apalache-extensions.html"><strong aria-hidden="true">24.</strong> Apalache extensions</a></span><ol class="section"><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/apalache-operators.html"><strong aria-hidden="true">24.1.</strong> Apalache module</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/variants.html"><strong aria-hidden="true">24.2.</strong> Variants</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/option-types.html"><strong aria-hidden="true">24.3.</strong> Option types</a></span></li></ol><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/user-operators.html"><strong aria-hidden="true">25.</strong> User-defined operators</a></span><ol class="section"><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/user/top-level-operators.html"><strong aria-hidden="true">25.1.</strong> Top-level operator definitions</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/user/let-in.html"><strong aria-hidden="true">25.2.</strong> LET-IN definitions</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/user/higher-order-operators.html"><strong aria-hidden="true">25.3.</strong> Higher-order operators definitions</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/user/lambdas.html"><strong aria-hidden="true">25.4.</strong> Anonymous operator definitions</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/user/local-operators.html"><strong aria-hidden="true">25.5.</strong> Local operator definitions</a></span></li></ol><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="lang/modules.html"><strong aria-hidden="true">26.</strong> Modules, Extends, and Instances</a></span></li><li class="chapter-item expanded "><li class="part-title">Idiomatic TLA+</li></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="idiomatic/index.html"><strong aria-hidden="true">27.</strong> Introduction</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="idiomatic/000keep-minimum-state-variables.html"><strong aria-hidden="true">28.</strong> Keep state variables to the minimum</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="idiomatic/001assignments.html"><strong aria-hidden="true">29.</strong> Update state variables with assignments</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="idiomatic/002primes.html"><strong aria-hidden="true">30.</strong> Apply primes only to state variables</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="idiomatic/007if-then-else.html"><strong aria-hidden="true">31.</strong> Use Boolean operators in actions, not IF-THEN-ELSE</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="idiomatic/003record-sets.html"><strong aria-hidden="true">32.</strong> Avoid sets of mixed records</a></span></li><li class="chapter-item expanded "><li class="part-title">Design Documents</li></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/001rfc-types.html"><strong aria-hidden="true">33.</strong> RFC 001: types and type annotations</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/002adr-types.html"><strong aria-hidden="true">34.</strong> ADR-002: types and type annotations</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/003adr-trex.html"><strong aria-hidden="true">35.</strong> ADR-003: transition executor (TRex)</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/004adr-annotations.html"><strong aria-hidden="true">36.</strong> ADR-004: code annotations</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/005adr-json.html"><strong aria-hidden="true">37.</strong> ADR-005: JSON Serialization Format</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/006rfc-unit-testing.html"><strong aria-hidden="true">38.</strong> RFC-006: unit tests and property-based tests</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/007adr-restructuring.html"><strong aria-hidden="true">39.</strong> ADR-007: restructuring</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/008adr-exceptions.html"><strong aria-hidden="true">40.</strong> ADR-008: exceptions</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/009adr-outputs.html"><strong aria-hidden="true">41.</strong> ADR-009: outputs</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/010rfc-transition-explorer.html"><strong aria-hidden="true">42.</strong> RFC-010: Implementation of Transition Exploration Server</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/011adr-smt-arrays.html"><strong aria-hidden="true">43.</strong> ADR-011: alternative SMT encoding using arrays</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/012adr-adopt-adr-template.html"><strong aria-hidden="true">44.</strong> ADR-012: Adopt an ADR Template</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/013adr-configuration.html"><strong aria-hidden="true">45.</strong> ADR-013: Configuration Management Component</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/014adr-precise-records.html"><strong aria-hidden="true">46.</strong> ADR-014: Precise type inference for records and variants</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/015adr-trace.html"><strong aria-hidden="true">47.</strong> ADR-015: ITF: informal trace format</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/016adr-retla.html"><strong aria-hidden="true">48.</strong> ADR-016: ReTLA: Relational TLA</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/017pdr-temporal.html"><strong aria-hidden="true">49.</strong> PDR-017: Checking temporal properties</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/018adr-inlining.html"><strong aria-hidden="true">50.</strong> ADR-018: Inlining in Apalache</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/019adr-harmonize-changelog.html"><strong aria-hidden="true">51.</strong> ADR-019: Harmonize changelog management</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/020adr-arenas.html"><strong aria-hidden="true">52.</strong> ADR-020: Improving membership in arenas</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/021rfc-prioritization.html"><strong aria-hidden="true">53.</strong> RFC-021: Prioritization of Work</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/022adr-unification-of-configs-and-options.html"><strong aria-hidden="true">54.</strong> ADR-022: Unify Configuration Management and &quot;Pass Options&quot;</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/023adr-trace-evaluation.html"><strong aria-hidden="true">55.</strong> ADR-023: Trace evaluation</a></span></li><li class="chapter-item expanded "><span class="chapter-link-wrapper"><a href="adr/024adr-arena-pass.html"><strong aria-hidden="true">56.</strong> ADR-024: Arena computation isolation</a></span></li></ol>';
        // Set the current, active page, and reveal it if it's hidden
        let current_page = document.location.href.toString().split('#')[0].split('?')[0];
        if (current_page.endsWith('/')) {
            current_page += 'index.html';
        }
        const links = Array.prototype.slice.call(this.querySelectorAll('a'));
        const l = links.length;
        for (let i = 0; i < l; ++i) {
            const link = links[i];
            const href = link.getAttribute('href');
            if (href && !href.startsWith('#') && !/^(?:[a-z+]+:)?\/\//.test(href)) {
                link.href = path_to_root + href;
            }
            // The 'index' page is supposed to alias the first chapter in the book.
            // Check both with and without the '.html' suffix to be robust against pretty URLs
            if (link.href.replace(/\.html$/, '') === current_page.replace(/\.html$/, '')
                || i === 0
                && path_to_root === ''
                && current_page.endsWith('/index.html')) {
                link.classList.add('active');
                let parent = link.parentElement;
                while (parent) {
                    if (parent.tagName === 'LI' && parent.classList.contains('chapter-item')) {
                        parent.classList.add('expanded');
                    }
                    parent = parent.parentElement;
                }
            }
        }
        // Track and set sidebar scroll position
        this.addEventListener('click', e => {
            if (e.target.tagName === 'A') {
                const clientRect = e.target.getBoundingClientRect();
                const sidebarRect = this.getBoundingClientRect();
                sessionStorage.setItem('sidebar-scroll-offset', clientRect.top - sidebarRect.top);
            }
        }, { passive: true });
        const sidebarScrollOffset = sessionStorage.getItem('sidebar-scroll-offset');
        sessionStorage.removeItem('sidebar-scroll-offset');
        if (sidebarScrollOffset !== null) {
            // preserve sidebar scroll position when navigating via links within sidebar
            const activeSection = this.querySelector('.active');
            if (activeSection) {
                const clientRect = activeSection.getBoundingClientRect();
                const sidebarRect = this.getBoundingClientRect();
                const currentOffset = clientRect.top - sidebarRect.top;
                this.scrollTop += currentOffset - parseFloat(sidebarScrollOffset);
            }
        } else {
            // scroll sidebar to current active section when navigating via
            // 'next/previous chapter' buttons
            const activeSection = document.querySelector('#mdbook-sidebar .active');
            if (activeSection) {
                activeSection.scrollIntoView({ block: 'center' });
            }
        }
        // Toggle buttons
        const sidebarAnchorToggles = document.querySelectorAll('.chapter-fold-toggle');
        function toggleSection(ev) {
            ev.currentTarget.parentElement.parentElement.classList.toggle('expanded');
        }
        Array.from(sidebarAnchorToggles).forEach(el => {
            el.addEventListener('click', toggleSection);
        });
    }
}
window.customElements.define('mdbook-sidebar-scrollbox', MDBookSidebarScrollbox);


// ---------------------------------------------------------------------------
// Support for dynamically adding headers to the sidebar.

(function() {
    // This is used to detect which direction the page has scrolled since the
    // last scroll event.
    let lastKnownScrollPosition = 0;
    // This is the threshold in px from the top of the screen where it will
    // consider a header the "current" header when scrolling down.
    const defaultDownThreshold = 150;
    // Same as defaultDownThreshold, except when scrolling up.
    const defaultUpThreshold = 300;
    // The threshold is a virtual horizontal line on the screen where it
    // considers the "current" header to be above the line. The threshold is
    // modified dynamically to handle headers that are near the bottom of the
    // screen, and to slightly offset the behavior when scrolling up vs down.
    let threshold = defaultDownThreshold;
    // This is used to disable updates while scrolling. This is needed when
    // clicking the header in the sidebar, which triggers a scroll event. It
    // is somewhat finicky to detect when the scroll has finished, so this
    // uses a relatively dumb system of disabling scroll updates for a short
    // time after the click.
    let disableScroll = false;
    // Array of header elements on the page.
    let headers;
    // Array of li elements that are initially collapsed headers in the sidebar.
    // I'm not sure why eslint seems to have a false positive here.
    // eslint-disable-next-line prefer-const
    let headerToggles = [];
    // This is a debugging tool for the threshold which you can enable in the console.
    let thresholdDebug = false;

    // Updates the threshold based on the scroll position.
    function updateThreshold() {
        const scrollTop = window.pageYOffset || document.documentElement.scrollTop;
        const windowHeight = window.innerHeight;
        const documentHeight = document.documentElement.scrollHeight;

        // The number of pixels below the viewport, at most documentHeight.
        // This is used to push the threshold down to the bottom of the page
        // as the user scrolls towards the bottom.
        const pixelsBelow = Math.max(0, documentHeight - (scrollTop + windowHeight));
        // The number of pixels above the viewport, at least defaultDownThreshold.
        // Similar to pixelsBelow, this is used to push the threshold back towards
        // the top when reaching the top of the page.
        const pixelsAbove = Math.max(0, defaultDownThreshold - scrollTop);
        // How much the threshold should be offset once it gets close to the
        // bottom of the page.
        const bottomAdd = Math.max(0, windowHeight - pixelsBelow - defaultDownThreshold);
        let adjustedBottomAdd = bottomAdd;

        // Adjusts bottomAdd for a small document. The calculation above
        // assumes the document is at least twice the windowheight in size. If
        // it is less than that, then bottomAdd needs to be shrunk
        // proportional to the difference in size.
        if (documentHeight < windowHeight * 2) {
            const maxPixelsBelow = documentHeight - windowHeight;
            const t = 1 - pixelsBelow / Math.max(1, maxPixelsBelow);
            const clamp = Math.max(0, Math.min(1, t));
            adjustedBottomAdd *= clamp;
        }

        let scrollingDown = true;
        if (scrollTop < lastKnownScrollPosition) {
            scrollingDown = false;
        }

        if (scrollingDown) {
            // When scrolling down, move the threshold up towards the default
            // downwards threshold position. If near the bottom of the page,
            // adjustedBottomAdd will offset the threshold towards the bottom
            // of the page.
            const amountScrolledDown = scrollTop - lastKnownScrollPosition;
            const adjustedDefault = defaultDownThreshold + adjustedBottomAdd;
            threshold = Math.max(adjustedDefault, threshold - amountScrolledDown);
        } else {
            // When scrolling up, move the threshold down towards the default
            // upwards threshold position. If near the bottom of the page,
            // quickly transition the threshold back up where it normally
            // belongs.
            const amountScrolledUp = lastKnownScrollPosition - scrollTop;
            const adjustedDefault = defaultUpThreshold - pixelsAbove
                + Math.max(0, adjustedBottomAdd - defaultDownThreshold);
            threshold = Math.min(adjustedDefault, threshold + amountScrolledUp);
        }

        if (documentHeight <= windowHeight) {
            threshold = 0;
        }

        if (thresholdDebug) {
            const id = 'mdbook-threshold-debug-data';
            let data = document.getElementById(id);
            if (data === null) {
                data = document.createElement('div');
                data.id = id;
                data.style.cssText = `
                    position: fixed;
                    top: 50px;
                    right: 10px;
                    background-color: 0xeeeeee;
                    z-index: 9999;
                    pointer-events: none;
                `;
                document.body.appendChild(data);
            }
            data.innerHTML = `
                <table>
                  <tr><td>documentHeight</td><td>${documentHeight.toFixed(1)}</td></tr>
                  <tr><td>windowHeight</td><td>${windowHeight.toFixed(1)}</td></tr>
                  <tr><td>scrollTop</td><td>${scrollTop.toFixed(1)}</td></tr>
                  <tr><td>pixelsAbove</td><td>${pixelsAbove.toFixed(1)}</td></tr>
                  <tr><td>pixelsBelow</td><td>${pixelsBelow.toFixed(1)}</td></tr>
                  <tr><td>bottomAdd</td><td>${bottomAdd.toFixed(1)}</td></tr>
                  <tr><td>adjustedBottomAdd</td><td>${adjustedBottomAdd.toFixed(1)}</td></tr>
                  <tr><td>scrollingDown</td><td>${scrollingDown}</td></tr>
                  <tr><td>threshold</td><td>${threshold.toFixed(1)}</td></tr>
                </table>
            `;
            drawDebugLine();
        }

        lastKnownScrollPosition = scrollTop;
    }

    function drawDebugLine() {
        if (!document.body) {
            return;
        }
        const id = 'mdbook-threshold-debug-line';
        const existingLine = document.getElementById(id);
        if (existingLine) {
            existingLine.remove();
        }
        const line = document.createElement('div');
        line.id = id;
        line.style.cssText = `
            position: fixed;
            top: ${threshold}px;
            left: 0;
            width: 100vw;
            height: 2px;
            background-color: red;
            z-index: 9999;
            pointer-events: none;
        `;
        document.body.appendChild(line);
    }

    function mdbookEnableThresholdDebug() {
        thresholdDebug = true;
        updateThreshold();
        drawDebugLine();
    }

    window.mdbookEnableThresholdDebug = mdbookEnableThresholdDebug;

    // Updates which headers in the sidebar should be expanded. If the current
    // header is inside a collapsed group, then it, and all its parents should
    // be expanded.
    function updateHeaderExpanded(currentA) {
        // Add expanded to all header-item li ancestors.
        let current = currentA.parentElement;
        while (current) {
            if (current.tagName === 'LI' && current.classList.contains('header-item')) {
                current.classList.add('expanded');
            }
            current = current.parentElement;
        }
    }

    // Updates which header is marked as the "current" header in the sidebar.
    // This is done with a virtual Y threshold, where headers at or below
    // that line will be considered the current one.
    function updateCurrentHeader() {
        if (!headers || !headers.length) {
            return;
        }

        // Reset the classes, which will be rebuilt below.
        const els = document.getElementsByClassName('current-header');
        for (const el of els) {
            el.classList.remove('current-header');
        }
        for (const toggle of headerToggles) {
            toggle.classList.remove('expanded');
        }

        // Find the last header that is above the threshold.
        let lastHeader = null;
        for (const header of headers) {
            const rect = header.getBoundingClientRect();
            if (rect.top <= threshold) {
                lastHeader = header;
            } else {
                break;
            }
        }
        if (lastHeader === null) {
            lastHeader = headers[0];
            const rect = lastHeader.getBoundingClientRect();
            const windowHeight = window.innerHeight;
            if (rect.top >= windowHeight) {
                return;
            }
        }

        // Get the anchor in the summary.
        const href = '#' + lastHeader.id;
        const a = [...document.querySelectorAll('.header-in-summary')]
            .find(element => element.getAttribute('href') === href);
        if (!a) {
            return;
        }

        a.classList.add('current-header');

        updateHeaderExpanded(a);
    }

    // Updates which header is "current" based on the threshold line.
    function reloadCurrentHeader() {
        if (disableScroll) {
            return;
        }
        updateThreshold();
        updateCurrentHeader();
    }


    // When clicking on a header in the sidebar, this adjusts the threshold so
    // that it is located next to the header. This is so that header becomes
    // "current".
    function headerThresholdClick(event) {
        // See disableScroll description why this is done.
        disableScroll = true;
        setTimeout(() => {
            disableScroll = false;
        }, 100);
        // requestAnimationFrame is used to delay the update of the "current"
        // header until after the scroll is done, and the header is in the new
        // position.
        requestAnimationFrame(() => {
            requestAnimationFrame(() => {
                // Closest is needed because if it has child elements like <code>.
                const a = event.target.closest('a');
                const href = a.getAttribute('href');
                const targetId = href.substring(1);
                const targetElement = document.getElementById(targetId);
                if (targetElement) {
                    threshold = targetElement.getBoundingClientRect().bottom;
                    updateCurrentHeader();
                }
            });
        });
    }

    // Takes the nodes from the given head and copies them over to the
    // destination, along with some filtering.
    function filterHeader(source, dest) {
        const clone = source.cloneNode(true);
        clone.querySelectorAll('mark').forEach(mark => {
            mark.replaceWith(...mark.childNodes);
        });
        dest.append(...clone.childNodes);
    }

    // Scans page for headers and adds them to the sidebar.
    document.addEventListener('DOMContentLoaded', function() {
        const activeSection = document.querySelector('#mdbook-sidebar .active');
        if (activeSection === null) {
            return;
        }

        const main = document.getElementsByTagName('main')[0];
        headers = Array.from(main.querySelectorAll('h2, h3, h4, h5, h6'))
            .filter(h => h.id !== '' && h.children.length && h.children[0].tagName === 'A');

        if (headers.length === 0) {
            return;
        }

        // Build a tree of headers in the sidebar.

        const stack = [];

        const firstLevel = parseInt(headers[0].tagName.charAt(1));
        for (let i = 1; i < firstLevel; i++) {
            const ol = document.createElement('ol');
            ol.classList.add('section');
            if (stack.length > 0) {
                stack[stack.length - 1].ol.appendChild(ol);
            }
            stack.push({level: i + 1, ol: ol});
        }

        // The level where it will start folding deeply nested headers.
        const foldLevel = 3;

        for (let i = 0; i < headers.length; i++) {
            const header = headers[i];
            const level = parseInt(header.tagName.charAt(1));

            const currentLevel = stack[stack.length - 1].level;
            if (level > currentLevel) {
                // Begin nesting to this level.
                for (let nextLevel = currentLevel + 1; nextLevel <= level; nextLevel++) {
                    const ol = document.createElement('ol');
                    ol.classList.add('section');
                    const last = stack[stack.length - 1];
                    const lastChild = last.ol.lastChild;
                    // Handle the case where jumping more than one nesting
                    // level, which doesn't have a list item to place this new
                    // list inside of.
                    if (lastChild) {
                        lastChild.appendChild(ol);
                    } else {
                        last.ol.appendChild(ol);
                    }
                    stack.push({level: nextLevel, ol: ol});
                }
            } else if (level < currentLevel) {
                while (stack.length > 1 && stack[stack.length - 1].level > level) {
                    stack.pop();
                }
            }

            const li = document.createElement('li');
            li.classList.add('header-item');
            li.classList.add('expanded');
            if (level < foldLevel) {
                li.classList.add('expanded');
            }
            const span = document.createElement('span');
            span.classList.add('chapter-link-wrapper');
            const a = document.createElement('a');
            span.appendChild(a);
            a.href = '#' + header.id;
            a.classList.add('header-in-summary');
            filterHeader(header.children[0], a);
            a.addEventListener('click', headerThresholdClick);
            const nextHeader = headers[i + 1];
            if (nextHeader !== undefined) {
                const nextLevel = parseInt(nextHeader.tagName.charAt(1));
                if (nextLevel > level && level >= foldLevel) {
                    const toggle = document.createElement('a');
                    toggle.classList.add('chapter-fold-toggle');
                    toggle.classList.add('header-toggle');
                    toggle.addEventListener('click', () => {
                        li.classList.toggle('expanded');
                    });
                    const toggleDiv = document.createElement('div');
                    toggleDiv.textContent = '❱';
                    toggle.appendChild(toggleDiv);
                    span.appendChild(toggle);
                    headerToggles.push(li);
                }
            }
            li.appendChild(span);

            const currentParent = stack[stack.length - 1];
            currentParent.ol.appendChild(li);
        }

        const onThisPage = document.createElement('div');
        onThisPage.classList.add('on-this-page');
        onThisPage.append(stack[0].ol);
        const activeItemSpan = activeSection.parentElement;
        activeItemSpan.after(onThisPage);
    });

    document.addEventListener('DOMContentLoaded', reloadCurrentHeader);
    document.addEventListener('scroll', reloadCurrentHeader, { passive: true });
})();

