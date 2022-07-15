/**
 * Language: TLA+
 * Author: Thomas Pani <thomas.pani@gmail.com>
 * Description: TLA+ is a high-level language for modeling programs and systems, especially concurrent and distributed ones.
 * Website: https://lamport.azurewebsites.net/tla/tla.html
 */
module.exports = function (hljs)
{
  return {
    // Auto-detection is hard: https://github.com/highlightjs/highlight.js/issues/1213
    disableAutodetect: true,
    case_insensitive: false,
    keywords:
      {
        keyword: 'ACTION ASSUME ASSUMPTION AXIOM BOOLEAN BY CASE CHOOSE CONSTANT CONSTANTS COROLLARY DEF DEFINE DEFS DOMAIN ELSE ENABLED EXCEPT EXTENDS FALSE HAVE HIDE IF IN INSTANCE LAMBDA LEMMA LET LOCAL MODULE NEW OBVIOUS OMITTED OTHER PICK PROOF PROPOSITION PROVE QED RECURSIVE STATE SUBSET SUFFICES TAKE TEMPORAL THEN THEOREM TRUE UNCHANGED UNION USE VARIABLE VARIABLES WITH WITNESS'
      },
    contains:
      [
        hljs.QUOTE_STRING_MODE,
        hljs.C_NUMBER_MODE,
        hljs.COMMENT(/\(\*/, /\*\)/),
        hljs.COMMENT(/\\\*/, /$/)
      ]
  }
}

