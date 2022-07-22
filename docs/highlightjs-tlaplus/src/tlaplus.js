/**
 * Language: TLA+
 * Author: Thomas Pani <thomas.pani@gmail.com>
 * Description: TLA+ is a high-level language for modeling programs and systems, especially concurrent and distributed ones.
 * Website: https://lamport.azurewebsites.net/tla/tla.html
 */
module.exports = function (hljs)
{
  return {
    aliases: ['tla'],
    // Auto-detection is hard: https://github.com/highlightjs/highlight.js/issues/1213
    disableAutodetect: true,
    case_insensitive: false,
    keywords:
      {
        // Specifying Systems p277, and
        // TLA+ Version 2: https://lamport.azurewebsites.net/tla/tla2-guide.pdf
        keyword: 'ACTION ASSUME ASSUMPTION AXIOM BY CASE CHOOSE CONSTANT CONSTANTS COROLLARY DEF DEFINE DEFS ELSE EXCEPT EXTENDS HAVE HIDE IF IN INSTANCE LAMBDA LEMMA LET LOCAL MODULE NEW OBVIOUS OMITTED ONLY OTHER PICK PROOF PROPOSITION PROVE QED RECURSIVE STATE SUFFICES TAKE TEMPORAL THEN THEOREM USE VARIABLE VARIABLES WITH WITNESS'
      },
    contains:
      [
        hljs.QUOTE_STRING_MODE,
        hljs.C_NUMBER_MODE,
        hljs.COMMENT(/\(\*/, /\*\)/),
        hljs.COMMENT(/\\\*/, /$/),
        // TLA+ specific modes, see Specifying Systems p277, and
        // TLA+ Version 2: https://lamport.azurewebsites.net/tla/tla2-guide.pdf
        {
          // TLA+ predefined identifiers
          className: 'literal',
          begin: /TRUE|FALSE|BOOLEAN|STRING/
        },
        {
          // TLA+ built-in operators like `\in`
          className: 'built_in',
          begin: /\\\w+/
        },
        {
          // TLA+ built-in operators like `DOMAIN`
          className: 'built_in',
          begin: /DOMAIN|ENABLED|SUBSET|UNCHANGED|UNION/
        },
        {
          // TLA+ built-in operators /\ and \/
          className: 'built_in',
          begin: /\\\/|\/\\/
        }
      ]
  }
}

