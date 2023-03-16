import * as React from 'react';
import React__default, { useRef, useState, useCallback, useContext, useMemo, Component, createElement } from 'react';
import { jsx } from 'react/jsx-runtime';
import ReactDOM from 'react-dom';

var classnames = {exports: {}};

/*!
	Copyright (c) 2018 Jed Watson.
	Licensed under the MIT License (MIT), see
	http://jedwatson.github.io/classnames
*/

(function (module) {
	/* global define */

	(function () {

	  var hasOwn = {}.hasOwnProperty;
	  function classNames() {
	    var classes = [];
	    for (var i = 0; i < arguments.length; i++) {
	      var arg = arguments[i];
	      if (!arg) continue;
	      var argType = typeof arg;
	      if (argType === 'string' || argType === 'number') {
	        classes.push(arg);
	      } else if (Array.isArray(arg)) {
	        if (arg.length) {
	          var inner = classNames.apply(null, arg);
	          if (inner) {
	            classes.push(inner);
	          }
	        }
	      } else if (argType === 'object') {
	        if (arg.toString !== Object.prototype.toString && !arg.toString.toString().includes('[native code]')) {
	          classes.push(arg.toString());
	          continue;
	        }
	        for (var key in arg) {
	          if (hasOwn.call(arg, key) && arg[key]) {
	            classes.push(key);
	          }
	        }
	      }
	    }
	    return classes.join(' ');
	  }
	  if (module.exports) {
	    classNames.default = classNames;
	    module.exports = classNames;
	  } else {
	    window.classNames = classNames;
	  }
	})();
} (classnames));

var classNames = classnames.exports;

function _extends() {
  _extends = Object.assign ? Object.assign.bind() : function (target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i];
      for (var key in source) {
        if (Object.prototype.hasOwnProperty.call(source, key)) {
          target[key] = source[key];
        }
      }
    }
    return target;
  };
  return _extends.apply(this, arguments);
}

function _objectWithoutPropertiesLoose(source, excluded) {
  if (source == null) return {};
  var target = {};
  var sourceKeys = Object.keys(source);
  var key, i;
  for (i = 0; i < sourceKeys.length; i++) {
    key = sourceKeys[i];
    if (excluded.indexOf(key) >= 0) continue;
    target[key] = source[key];
  }
  return target;
}

function defaultKey(key) {
  return 'default' + key.charAt(0).toUpperCase() + key.substr(1);
}

function _toPropertyKey(arg) {
  var key = _toPrimitive(arg, "string");
  return typeof key === "symbol" ? key : String(key);
}
function _toPrimitive(input, hint) {
  if (typeof input !== "object" || input === null) return input;
  var prim = input[Symbol.toPrimitive];
  if (prim !== undefined) {
    var res = prim.call(input, hint || "default");
    if (typeof res !== "object") return res;
    throw new TypeError("@@toPrimitive must return a primitive value.");
  }
  return (hint === "string" ? String : Number)(input);
}
function useUncontrolledProp(propValue, defaultValue, handler) {
  var wasPropRef = useRef(propValue !== undefined);
  var _useState = useState(defaultValue),
    stateValue = _useState[0],
    setState = _useState[1];
  var isProp = propValue !== undefined;
  var wasProp = wasPropRef.current;
  wasPropRef.current = isProp;
  /**
   * If a prop switches from controlled to Uncontrolled
   * reset its value to the defaultValue
   */

  if (!isProp && wasProp && stateValue !== defaultValue) {
    setState(defaultValue);
  }
  return [isProp ? propValue : stateValue, useCallback(function (value) {
    for (var _len = arguments.length, args = new Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
      args[_key - 1] = arguments[_key];
    }
    if (handler) handler.apply(void 0, [value].concat(args));
    setState(value);
  }, [handler])];
}
function useUncontrolled(props, config) {
  return Object.keys(config).reduce(function (result, fieldName) {
    var _extends2;
    var _ref = result,
      defaultValue = _ref[defaultKey(fieldName)],
      propsValue = _ref[fieldName],
      rest = _objectWithoutPropertiesLoose(_ref, [defaultKey(fieldName), fieldName].map(_toPropertyKey));
    var handlerName = config[fieldName];
    var _useUncontrolledProp = useUncontrolledProp(propsValue, defaultValue, props[handlerName]),
      value = _useUncontrolledProp[0],
      handler = _useUncontrolledProp[1];
    return _extends({}, rest, (_extends2 = {}, _extends2[fieldName] = value, _extends2[handlerName] = handler, _extends2));
  }, props);
}

function _setPrototypeOf(o, p) {
  _setPrototypeOf = Object.setPrototypeOf ? Object.setPrototypeOf.bind() : function _setPrototypeOf(o, p) {
    o.__proto__ = p;
    return o;
  };
  return _setPrototypeOf(o, p);
}

function _inheritsLoose(subClass, superClass) {
  subClass.prototype = Object.create(superClass.prototype);
  subClass.prototype.constructor = subClass;
  _setPrototypeOf(subClass, superClass);
}

const DEFAULT_BREAKPOINTS = ['xxl', 'xl', 'lg', 'md', 'sm', 'xs'];
const DEFAULT_MIN_BREAKPOINT = 'xs';
const ThemeContext = /*#__PURE__*/React.createContext({
  prefixes: {},
  breakpoints: DEFAULT_BREAKPOINTS,
  minBreakpoint: DEFAULT_MIN_BREAKPOINT
});
function useBootstrapPrefix(prefix, defaultPrefix) {
  const {
    prefixes
  } = useContext(ThemeContext);
  return prefix || prefixes[defaultPrefix] || defaultPrefix;
}

/**
 * Returns the owner document of a given element.
 * 
 * @param node the element
 */
function ownerDocument(node) {
  return node && node.ownerDocument || document;
}

/**
 * Returns the owner window of a given element.
 * 
 * @param node the element
 */

function ownerWindow(node) {
  var doc = ownerDocument(node);
  return doc && doc.defaultView || window;
}

/**
 * Returns one or all computed style properties of an element.
 * 
 * @param node the element
 * @param psuedoElement the style property
 */

function getComputedStyle(node, psuedoElement) {
  return ownerWindow(node).getComputedStyle(node, psuedoElement);
}

var rUpper = /([A-Z])/g;
function hyphenate(string) {
  return string.replace(rUpper, '-$1').toLowerCase();
}

/**
 * Copyright 2013-2014, Facebook, Inc.
 * All rights reserved.
 * https://github.com/facebook/react/blob/2aeb8a2a6beb00617a4217f7f8284924fa2ad819/src/vendor/core/hyphenateStyleName.js
 */
var msPattern = /^ms-/;
function hyphenateStyleName(string) {
  return hyphenate(string).replace(msPattern, '-ms-');
}

var supportedTransforms = /^((translate|rotate|scale)(X|Y|Z|3d)?|matrix(3d)?|perspective|skew(X|Y)?)$/i;
function isTransform(value) {
  return !!(value && supportedTransforms.test(value));
}

function style(node, property) {
  var css = '';
  var transforms = '';
  if (typeof property === 'string') {
    return node.style.getPropertyValue(hyphenateStyleName(property)) || getComputedStyle(node).getPropertyValue(hyphenateStyleName(property));
  }
  Object.keys(property).forEach(function (key) {
    var value = property[key];
    if (!value && value !== 0) {
      node.style.removeProperty(hyphenateStyleName(key));
    } else if (isTransform(key)) {
      transforms += key + "(" + value + ") ";
    } else {
      css += hyphenateStyleName(key) + ": " + value + ";";
    }
  });
  if (transforms) {
    css += "transform: " + transforms + ";";
  }
  node.style.cssText += ";" + css;
}

var propTypes = {exports: {}};

var reactIs = {exports: {}};

var reactIs_development = {};

/** @license React v16.13.1
 * react-is.development.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var hasRequiredReactIs_development;

function requireReactIs_development () {
	if (hasRequiredReactIs_development) return reactIs_development;
	hasRequiredReactIs_development = 1;

	{
	  (function () {

	    // The Symbol used to tag the ReactElement-like types. If there is no native Symbol
	    // nor polyfill, then a plain number is used for performance.
	    var hasSymbol = typeof Symbol === 'function' && Symbol.for;
	    var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
	    var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
	    var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
	    var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
	    var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
	    var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
	    var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
	    // (unstable) APIs that have been removed. Can we remove the symbols?

	    var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
	    var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
	    var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
	    var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
	    var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
	    var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
	    var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
	    var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
	    var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
	    var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
	    var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;
	    function isValidElementType(type) {
	      return typeof type === 'string' || typeof type === 'function' ||
	      // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
	      type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
	    }
	    function typeOf(object) {
	      if (typeof object === 'object' && object !== null) {
	        var $$typeof = object.$$typeof;
	        switch ($$typeof) {
	          case REACT_ELEMENT_TYPE:
	            var type = object.type;
	            switch (type) {
	              case REACT_ASYNC_MODE_TYPE:
	              case REACT_CONCURRENT_MODE_TYPE:
	              case REACT_FRAGMENT_TYPE:
	              case REACT_PROFILER_TYPE:
	              case REACT_STRICT_MODE_TYPE:
	              case REACT_SUSPENSE_TYPE:
	                return type;
	              default:
	                var $$typeofType = type && type.$$typeof;
	                switch ($$typeofType) {
	                  case REACT_CONTEXT_TYPE:
	                  case REACT_FORWARD_REF_TYPE:
	                  case REACT_LAZY_TYPE:
	                  case REACT_MEMO_TYPE:
	                  case REACT_PROVIDER_TYPE:
	                    return $$typeofType;
	                  default:
	                    return $$typeof;
	                }
	            }
	          case REACT_PORTAL_TYPE:
	            return $$typeof;
	        }
	      }
	      return undefined;
	    } // AsyncMode is deprecated along with isAsyncMode

	    var AsyncMode = REACT_ASYNC_MODE_TYPE;
	    var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
	    var ContextConsumer = REACT_CONTEXT_TYPE;
	    var ContextProvider = REACT_PROVIDER_TYPE;
	    var Element = REACT_ELEMENT_TYPE;
	    var ForwardRef = REACT_FORWARD_REF_TYPE;
	    var Fragment = REACT_FRAGMENT_TYPE;
	    var Lazy = REACT_LAZY_TYPE;
	    var Memo = REACT_MEMO_TYPE;
	    var Portal = REACT_PORTAL_TYPE;
	    var Profiler = REACT_PROFILER_TYPE;
	    var StrictMode = REACT_STRICT_MODE_TYPE;
	    var Suspense = REACT_SUSPENSE_TYPE;
	    var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

	    function isAsyncMode(object) {
	      {
	        if (!hasWarnedAboutDeprecatedIsAsyncMode) {
	          hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

	          console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
	        }
	      }
	      return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
	    }
	    function isConcurrentMode(object) {
	      return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
	    }
	    function isContextConsumer(object) {
	      return typeOf(object) === REACT_CONTEXT_TYPE;
	    }
	    function isContextProvider(object) {
	      return typeOf(object) === REACT_PROVIDER_TYPE;
	    }
	    function isElement(object) {
	      return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
	    }
	    function isForwardRef(object) {
	      return typeOf(object) === REACT_FORWARD_REF_TYPE;
	    }
	    function isFragment(object) {
	      return typeOf(object) === REACT_FRAGMENT_TYPE;
	    }
	    function isLazy(object) {
	      return typeOf(object) === REACT_LAZY_TYPE;
	    }
	    function isMemo(object) {
	      return typeOf(object) === REACT_MEMO_TYPE;
	    }
	    function isPortal(object) {
	      return typeOf(object) === REACT_PORTAL_TYPE;
	    }
	    function isProfiler(object) {
	      return typeOf(object) === REACT_PROFILER_TYPE;
	    }
	    function isStrictMode(object) {
	      return typeOf(object) === REACT_STRICT_MODE_TYPE;
	    }
	    function isSuspense(object) {
	      return typeOf(object) === REACT_SUSPENSE_TYPE;
	    }
	    reactIs_development.AsyncMode = AsyncMode;
	    reactIs_development.ConcurrentMode = ConcurrentMode;
	    reactIs_development.ContextConsumer = ContextConsumer;
	    reactIs_development.ContextProvider = ContextProvider;
	    reactIs_development.Element = Element;
	    reactIs_development.ForwardRef = ForwardRef;
	    reactIs_development.Fragment = Fragment;
	    reactIs_development.Lazy = Lazy;
	    reactIs_development.Memo = Memo;
	    reactIs_development.Portal = Portal;
	    reactIs_development.Profiler = Profiler;
	    reactIs_development.StrictMode = StrictMode;
	    reactIs_development.Suspense = Suspense;
	    reactIs_development.isAsyncMode = isAsyncMode;
	    reactIs_development.isConcurrentMode = isConcurrentMode;
	    reactIs_development.isContextConsumer = isContextConsumer;
	    reactIs_development.isContextProvider = isContextProvider;
	    reactIs_development.isElement = isElement;
	    reactIs_development.isForwardRef = isForwardRef;
	    reactIs_development.isFragment = isFragment;
	    reactIs_development.isLazy = isLazy;
	    reactIs_development.isMemo = isMemo;
	    reactIs_development.isPortal = isPortal;
	    reactIs_development.isProfiler = isProfiler;
	    reactIs_development.isStrictMode = isStrictMode;
	    reactIs_development.isSuspense = isSuspense;
	    reactIs_development.isValidElementType = isValidElementType;
	    reactIs_development.typeOf = typeOf;
	  })();
	}
	return reactIs_development;
}

var hasRequiredReactIs;

function requireReactIs () {
	if (hasRequiredReactIs) return reactIs.exports;
	hasRequiredReactIs = 1;
	(function (module) {

		{
		  module.exports = requireReactIs_development();
		}
} (reactIs));
	return reactIs.exports;
}

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/

var objectAssign;
var hasRequiredObjectAssign;

function requireObjectAssign () {
	if (hasRequiredObjectAssign) return objectAssign;
	hasRequiredObjectAssign = 1;

	/* eslint-disable no-unused-vars */
	var getOwnPropertySymbols = Object.getOwnPropertySymbols;
	var hasOwnProperty = Object.prototype.hasOwnProperty;
	var propIsEnumerable = Object.prototype.propertyIsEnumerable;
	function toObject(val) {
	  if (val === null || val === undefined) {
	    throw new TypeError('Object.assign cannot be called with null or undefined');
	  }
	  return Object(val);
	}
	function shouldUseNative() {
	  try {
	    if (!Object.assign) {
	      return false;
	    }

	    // Detect buggy property enumeration order in older V8 versions.

	    // https://bugs.chromium.org/p/v8/issues/detail?id=4118
	    var test1 = new String('abc'); // eslint-disable-line no-new-wrappers
	    test1[5] = 'de';
	    if (Object.getOwnPropertyNames(test1)[0] === '5') {
	      return false;
	    }

	    // https://bugs.chromium.org/p/v8/issues/detail?id=3056
	    var test2 = {};
	    for (var i = 0; i < 10; i++) {
	      test2['_' + String.fromCharCode(i)] = i;
	    }
	    var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
	      return test2[n];
	    });
	    if (order2.join('') !== '0123456789') {
	      return false;
	    }

	    // https://bugs.chromium.org/p/v8/issues/detail?id=3056
	    var test3 = {};
	    'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
	      test3[letter] = letter;
	    });
	    if (Object.keys(Object.assign({}, test3)).join('') !== 'abcdefghijklmnopqrst') {
	      return false;
	    }
	    return true;
	  } catch (err) {
	    // We don't expect any of the above to throw, but better to be safe.
	    return false;
	  }
	}
	objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
	  var from;
	  var to = toObject(target);
	  var symbols;
	  for (var s = 1; s < arguments.length; s++) {
	    from = Object(arguments[s]);
	    for (var key in from) {
	      if (hasOwnProperty.call(from, key)) {
	        to[key] = from[key];
	      }
	    }
	    if (getOwnPropertySymbols) {
	      symbols = getOwnPropertySymbols(from);
	      for (var i = 0; i < symbols.length; i++) {
	        if (propIsEnumerable.call(from, symbols[i])) {
	          to[symbols[i]] = from[symbols[i]];
	        }
	      }
	    }
	  }
	  return to;
	};
	return objectAssign;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret_1;
var hasRequiredReactPropTypesSecret;

function requireReactPropTypesSecret () {
	if (hasRequiredReactPropTypesSecret) return ReactPropTypesSecret_1;
	hasRequiredReactPropTypesSecret = 1;

	var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';
	ReactPropTypesSecret_1 = ReactPropTypesSecret;
	return ReactPropTypesSecret_1;
}

var has;
var hasRequiredHas;

function requireHas () {
	if (hasRequiredHas) return has;
	hasRequiredHas = 1;
	has = Function.call.bind(Object.prototype.hasOwnProperty);
	return has;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var checkPropTypes_1;
var hasRequiredCheckPropTypes;

function requireCheckPropTypes () {
	if (hasRequiredCheckPropTypes) return checkPropTypes_1;
	hasRequiredCheckPropTypes = 1;

	var printWarning = function () {};
	{
	  var ReactPropTypesSecret = requireReactPropTypesSecret();
	  var loggedTypeFailures = {};
	  var has = requireHas();
	  printWarning = function (text) {
	    var message = 'Warning: ' + text;
	    if (typeof console !== 'undefined') {
	      console.error(message);
	    }
	    try {
	      // --- Welcome to debugging React ---
	      // This error was thrown as a convenience so that you can use this stack
	      // to find the callsite that caused this warning to fire.
	      throw new Error(message);
	    } catch (x) {/**/}
	  };
	}

	/**
	 * Assert that the values match with the type specs.
	 * Error messages are memorized and will only be shown once.
	 *
	 * @param {object} typeSpecs Map of name to a ReactPropType
	 * @param {object} values Runtime values that need to be type-checked
	 * @param {string} location e.g. "prop", "context", "child context"
	 * @param {string} componentName Name of the component for error messages.
	 * @param {?Function} getStack Returns the component stack.
	 * @private
	 */
	function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
	  {
	    for (var typeSpecName in typeSpecs) {
	      if (has(typeSpecs, typeSpecName)) {
	        var error;
	        // Prop type validation may throw. In case they do, we don't want to
	        // fail the render phase where it didn't fail before. So we log it.
	        // After these have been cleaned up, we'll let them throw.
	        try {
	          // This is intentionally an invariant that gets caught. It's the same
	          // behavior as without this statement except with a better message.
	          if (typeof typeSpecs[typeSpecName] !== 'function') {
	            var err = Error((componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' + 'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.' + 'This often happens because of typos such as `PropTypes.function` instead of `PropTypes.func`.');
	            err.name = 'Invariant Violation';
	            throw err;
	          }
	          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret);
	        } catch (ex) {
	          error = ex;
	        }
	        if (error && !(error instanceof Error)) {
	          printWarning((componentName || 'React class') + ': type specification of ' + location + ' `' + typeSpecName + '` is invalid; the type checker ' + 'function must return `null` or an `Error` but returned a ' + typeof error + '. ' + 'You may have forgotten to pass an argument to the type checker ' + 'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' + 'shape all require an argument).');
	        }
	        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
	          // Only monitor this failure once because there tends to be a lot of the
	          // same error.
	          loggedTypeFailures[error.message] = true;
	          var stack = getStack ? getStack() : '';
	          printWarning('Failed ' + location + ' type: ' + error.message + (stack != null ? stack : ''));
	        }
	      }
	    }
	  }
	}

	/**
	 * Resets warning cache when testing.
	 *
	 * @private
	 */
	checkPropTypes.resetWarningCache = function () {
	  {
	    loggedTypeFailures = {};
	  }
	};
	checkPropTypes_1 = checkPropTypes;
	return checkPropTypes_1;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var factoryWithTypeCheckers;
var hasRequiredFactoryWithTypeCheckers;

function requireFactoryWithTypeCheckers () {
	if (hasRequiredFactoryWithTypeCheckers) return factoryWithTypeCheckers;
	hasRequiredFactoryWithTypeCheckers = 1;

	var ReactIs = requireReactIs();
	var assign = requireObjectAssign();
	var ReactPropTypesSecret = requireReactPropTypesSecret();
	var has = requireHas();
	var checkPropTypes = requireCheckPropTypes();
	var printWarning = function () {};
	{
	  printWarning = function (text) {
	    var message = 'Warning: ' + text;
	    if (typeof console !== 'undefined') {
	      console.error(message);
	    }
	    try {
	      // --- Welcome to debugging React ---
	      // This error was thrown as a convenience so that you can use this stack
	      // to find the callsite that caused this warning to fire.
	      throw new Error(message);
	    } catch (x) {}
	  };
	}
	function emptyFunctionThatReturnsNull() {
	  return null;
	}
	factoryWithTypeCheckers = function (isValidElement, throwOnDirectAccess) {
	  /* global Symbol */
	  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
	  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

	  /**
	   * Returns the iterator method function contained on the iterable object.
	   *
	   * Be sure to invoke the function with the iterable as context:
	   *
	   *     var iteratorFn = getIteratorFn(myIterable);
	   *     if (iteratorFn) {
	   *       var iterator = iteratorFn.call(myIterable);
	   *       ...
	   *     }
	   *
	   * @param {?object} maybeIterable
	   * @return {?function}
	   */
	  function getIteratorFn(maybeIterable) {
	    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
	    if (typeof iteratorFn === 'function') {
	      return iteratorFn;
	    }
	  }

	  /**
	   * Collection of methods that allow declaration and validation of props that are
	   * supplied to React components. Example usage:
	   *
	   *   var Props = require('ReactPropTypes');
	   *   var MyArticle = React.createClass({
	   *     propTypes: {
	   *       // An optional string prop named "description".
	   *       description: Props.string,
	   *
	   *       // A required enum prop named "category".
	   *       category: Props.oneOf(['News','Photos']).isRequired,
	   *
	   *       // A prop named "dialog" that requires an instance of Dialog.
	   *       dialog: Props.instanceOf(Dialog).isRequired
	   *     },
	   *     render: function() { ... }
	   *   });
	   *
	   * A more formal specification of how these methods are used:
	   *
	   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
	   *   decl := ReactPropTypes.{type}(.isRequired)?
	   *
	   * Each and every declaration produces a function with the same signature. This
	   * allows the creation of custom validation functions. For example:
	   *
	   *  var MyLink = React.createClass({
	   *    propTypes: {
	   *      // An optional string or URI prop named "href".
	   *      href: function(props, propName, componentName) {
	   *        var propValue = props[propName];
	   *        if (propValue != null && typeof propValue !== 'string' &&
	   *            !(propValue instanceof URI)) {
	   *          return new Error(
	   *            'Expected a string or an URI for ' + propName + ' in ' +
	   *            componentName
	   *          );
	   *        }
	   *      }
	   *    },
	   *    render: function() {...}
	   *  });
	   *
	   * @internal
	   */

	  var ANONYMOUS = '<<anonymous>>';

	  // Important!
	  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
	  var ReactPropTypes = {
	    array: createPrimitiveTypeChecker('array'),
	    bigint: createPrimitiveTypeChecker('bigint'),
	    bool: createPrimitiveTypeChecker('boolean'),
	    func: createPrimitiveTypeChecker('function'),
	    number: createPrimitiveTypeChecker('number'),
	    object: createPrimitiveTypeChecker('object'),
	    string: createPrimitiveTypeChecker('string'),
	    symbol: createPrimitiveTypeChecker('symbol'),
	    any: createAnyTypeChecker(),
	    arrayOf: createArrayOfTypeChecker,
	    element: createElementTypeChecker(),
	    elementType: createElementTypeTypeChecker(),
	    instanceOf: createInstanceTypeChecker,
	    node: createNodeChecker(),
	    objectOf: createObjectOfTypeChecker,
	    oneOf: createEnumTypeChecker,
	    oneOfType: createUnionTypeChecker,
	    shape: createShapeTypeChecker,
	    exact: createStrictShapeTypeChecker
	  };

	  /**
	   * inlined Object.is polyfill to avoid requiring consumers ship their own
	   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
	   */
	  /*eslint-disable no-self-compare*/
	  function is(x, y) {
	    // SameValue algorithm
	    if (x === y) {
	      // Steps 1-5, 7-10
	      // Steps 6.b-6.e: +0 != -0
	      return x !== 0 || 1 / x === 1 / y;
	    } else {
	      // Step 6.a: NaN == NaN
	      return x !== x && y !== y;
	    }
	  }
	  /*eslint-enable no-self-compare*/

	  /**
	   * We use an Error-like object for backward compatibility as people may call
	   * PropTypes directly and inspect their output. However, we don't use real
	   * Errors anymore. We don't inspect their stack anyway, and creating them
	   * is prohibitively expensive if they are created too often, such as what
	   * happens in oneOfType() for any type before the one that matched.
	   */
	  function PropTypeError(message, data) {
	    this.message = message;
	    this.data = data && typeof data === 'object' ? data : {};
	    this.stack = '';
	  }
	  // Make `instanceof Error` still work for returned errors.
	  PropTypeError.prototype = Error.prototype;
	  function createChainableTypeChecker(validate) {
	    {
	      var manualPropTypeCallCache = {};
	      var manualPropTypeWarningCount = 0;
	    }
	    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
	      componentName = componentName || ANONYMOUS;
	      propFullName = propFullName || propName;
	      if (secret !== ReactPropTypesSecret) {
	        if (throwOnDirectAccess) {
	          // New behavior only for users of `prop-types` package
	          var err = new Error('Calling PropTypes validators directly is not supported by the `prop-types` package. ' + 'Use `PropTypes.checkPropTypes()` to call them. ' + 'Read more at http://fb.me/use-check-prop-types');
	          err.name = 'Invariant Violation';
	          throw err;
	        } else if (typeof console !== 'undefined') {
	          // Old behavior for people using React.PropTypes
	          var cacheKey = componentName + ':' + propName;
	          if (!manualPropTypeCallCache[cacheKey] &&
	          // Avoid spamming the console because they are often not actionable except for lib authors
	          manualPropTypeWarningCount < 3) {
	            printWarning('You are manually calling a React.PropTypes validation ' + 'function for the `' + propFullName + '` prop on `' + componentName + '`. This is deprecated ' + 'and will throw in the standalone `prop-types` package. ' + 'You may be seeing this warning due to a third-party PropTypes ' + 'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.');
	            manualPropTypeCallCache[cacheKey] = true;
	            manualPropTypeWarningCount++;
	          }
	        }
	      }
	      if (props[propName] == null) {
	        if (isRequired) {
	          if (props[propName] === null) {
	            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
	          }
	          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
	        }
	        return null;
	      } else {
	        return validate(props, propName, componentName, location, propFullName);
	      }
	    }
	    var chainedCheckType = checkType.bind(null, false);
	    chainedCheckType.isRequired = checkType.bind(null, true);
	    return chainedCheckType;
	  }
	  function createPrimitiveTypeChecker(expectedType) {
	    function validate(props, propName, componentName, location, propFullName, secret) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== expectedType) {
	        // `propValue` being instance of, say, date/regexp, pass the 'object'
	        // check, but we can offer a more precise error message here rather than
	        // 'of type `object`'.
	        var preciseType = getPreciseType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'), {
	          expectedType: expectedType
	        });
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }
	  function createAnyTypeChecker() {
	    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
	  }
	  function createArrayOfTypeChecker(typeChecker) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (typeof typeChecker !== 'function') {
	        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
	      }
	      var propValue = props[propName];
	      if (!Array.isArray(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
	      }
	      for (var i = 0; i < propValue.length; i++) {
	        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret);
	        if (error instanceof Error) {
	          return error;
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }
	  function createElementTypeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      if (!isValidElement(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }
	  function createElementTypeTypeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      if (!ReactIs.isValidElementType(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }
	  function createInstanceTypeChecker(expectedClass) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (!(props[propName] instanceof expectedClass)) {
	        var expectedClassName = expectedClass.name || ANONYMOUS;
	        var actualClassName = getClassName(props[propName]);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }
	  function createEnumTypeChecker(expectedValues) {
	    if (!Array.isArray(expectedValues)) {
	      {
	        if (arguments.length > 1) {
	          printWarning('Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' + 'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).');
	        } else {
	          printWarning('Invalid argument supplied to oneOf, expected an array.');
	        }
	      }
	      return emptyFunctionThatReturnsNull;
	    }
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      for (var i = 0; i < expectedValues.length; i++) {
	        if (is(propValue, expectedValues[i])) {
	          return null;
	        }
	      }
	      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
	        var type = getPreciseType(value);
	        if (type === 'symbol') {
	          return String(value);
	        }
	        return value;
	      });
	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
	    }
	    return createChainableTypeChecker(validate);
	  }
	  function createObjectOfTypeChecker(typeChecker) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (typeof typeChecker !== 'function') {
	        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
	      }
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
	      }
	      for (var key in propValue) {
	        if (has(propValue, key)) {
	          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	          if (error instanceof Error) {
	            return error;
	          }
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }
	  function createUnionTypeChecker(arrayOfTypeCheckers) {
	    if (!Array.isArray(arrayOfTypeCheckers)) {
	      printWarning('Invalid argument supplied to oneOfType, expected an instance of array.') ;
	      return emptyFunctionThatReturnsNull;
	    }
	    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	      var checker = arrayOfTypeCheckers[i];
	      if (typeof checker !== 'function') {
	        printWarning('Invalid argument supplied to oneOfType. Expected an array of check functions, but ' + 'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.');
	        return emptyFunctionThatReturnsNull;
	      }
	    }
	    function validate(props, propName, componentName, location, propFullName) {
	      var expectedTypes = [];
	      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	        var checker = arrayOfTypeCheckers[i];
	        var checkerResult = checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret);
	        if (checkerResult == null) {
	          return null;
	        }
	        if (checkerResult.data && has(checkerResult.data, 'expectedType')) {
	          expectedTypes.push(checkerResult.data.expectedType);
	        }
	      }
	      var expectedTypesMessage = expectedTypes.length > 0 ? ', expected one of type [' + expectedTypes.join(', ') + ']' : '';
	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`' + expectedTypesMessage + '.'));
	    }
	    return createChainableTypeChecker(validate);
	  }
	  function createNodeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (!isNode(props[propName])) {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }
	  function invalidValidatorError(componentName, location, propFullName, key, type) {
	    return new PropTypeError((componentName || 'React class') + ': ' + location + ' type `' + propFullName + '.' + key + '` is invalid; ' + 'it must be a function, usually from the `prop-types` package, but received `' + type + '`.');
	  }
	  function createShapeTypeChecker(shapeTypes) {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
	      }
	      for (var key in shapeTypes) {
	        var checker = shapeTypes[key];
	        if (typeof checker !== 'function') {
	          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	        if (error) {
	          return error;
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }
	  function createStrictShapeTypeChecker(shapeTypes) {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
	      }
	      // We need to check all keys in case some are required but missing from props.
	      var allKeys = assign({}, props[propName], shapeTypes);
	      for (var key in allKeys) {
	        var checker = shapeTypes[key];
	        if (has(shapeTypes, key) && typeof checker !== 'function') {
	          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
	        }
	        if (!checker) {
	          return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' + '\nBad object: ' + JSON.stringify(props[propName], null, '  ') + '\nValid keys: ' + JSON.stringify(Object.keys(shapeTypes), null, '  '));
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	        if (error) {
	          return error;
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }
	  function isNode(propValue) {
	    switch (typeof propValue) {
	      case 'number':
	      case 'string':
	      case 'undefined':
	        return true;
	      case 'boolean':
	        return !propValue;
	      case 'object':
	        if (Array.isArray(propValue)) {
	          return propValue.every(isNode);
	        }
	        if (propValue === null || isValidElement(propValue)) {
	          return true;
	        }
	        var iteratorFn = getIteratorFn(propValue);
	        if (iteratorFn) {
	          var iterator = iteratorFn.call(propValue);
	          var step;
	          if (iteratorFn !== propValue.entries) {
	            while (!(step = iterator.next()).done) {
	              if (!isNode(step.value)) {
	                return false;
	              }
	            }
	          } else {
	            // Iterator will provide entry [k,v] tuples rather than values.
	            while (!(step = iterator.next()).done) {
	              var entry = step.value;
	              if (entry) {
	                if (!isNode(entry[1])) {
	                  return false;
	                }
	              }
	            }
	          }
	        } else {
	          return false;
	        }
	        return true;
	      default:
	        return false;
	    }
	  }
	  function isSymbol(propType, propValue) {
	    // Native Symbol.
	    if (propType === 'symbol') {
	      return true;
	    }

	    // falsy value can't be a Symbol
	    if (!propValue) {
	      return false;
	    }

	    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
	    if (propValue['@@toStringTag'] === 'Symbol') {
	      return true;
	    }

	    // Fallback for non-spec compliant Symbols which are polyfilled.
	    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
	      return true;
	    }
	    return false;
	  }

	  // Equivalent of `typeof` but with special handling for array and regexp.
	  function getPropType(propValue) {
	    var propType = typeof propValue;
	    if (Array.isArray(propValue)) {
	      return 'array';
	    }
	    if (propValue instanceof RegExp) {
	      // Old webkits (at least until Android 4.0) return 'function' rather than
	      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
	      // passes PropTypes.object.
	      return 'object';
	    }
	    if (isSymbol(propType, propValue)) {
	      return 'symbol';
	    }
	    return propType;
	  }

	  // This handles more types than `getPropType`. Only used for error messages.
	  // See `createPrimitiveTypeChecker`.
	  function getPreciseType(propValue) {
	    if (typeof propValue === 'undefined' || propValue === null) {
	      return '' + propValue;
	    }
	    var propType = getPropType(propValue);
	    if (propType === 'object') {
	      if (propValue instanceof Date) {
	        return 'date';
	      } else if (propValue instanceof RegExp) {
	        return 'regexp';
	      }
	    }
	    return propType;
	  }

	  // Returns a string that is postfixed to a warning about an invalid type.
	  // For example, "undefined" or "of type array"
	  function getPostfixForTypeWarning(value) {
	    var type = getPreciseType(value);
	    switch (type) {
	      case 'array':
	      case 'object':
	        return 'an ' + type;
	      case 'boolean':
	      case 'date':
	      case 'regexp':
	        return 'a ' + type;
	      default:
	        return type;
	    }
	  }

	  // Returns class name of the object, if any.
	  function getClassName(propValue) {
	    if (!propValue.constructor || !propValue.constructor.name) {
	      return ANONYMOUS;
	    }
	    return propValue.constructor.name;
	  }
	  ReactPropTypes.checkPropTypes = checkPropTypes;
	  ReactPropTypes.resetWarningCache = checkPropTypes.resetWarningCache;
	  ReactPropTypes.PropTypes = ReactPropTypes;
	  return ReactPropTypes;
	};
	return factoryWithTypeCheckers;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

{
  var ReactIs = requireReactIs();

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  propTypes.exports = requireFactoryWithTypeCheckers()(ReactIs.isElement, throwOnDirectAccess);
}

var config = {
  disabled: false
};

var timeoutsShape = propTypes.exports.oneOfType([propTypes.exports.number, propTypes.exports.shape({
  enter: propTypes.exports.number,
  exit: propTypes.exports.number,
  appear: propTypes.exports.number
}).isRequired]) ;
propTypes.exports.oneOfType([propTypes.exports.string, propTypes.exports.shape({
  enter: propTypes.exports.string,
  exit: propTypes.exports.string,
  active: propTypes.exports.string
}), propTypes.exports.shape({
  enter: propTypes.exports.string,
  enterDone: propTypes.exports.string,
  enterActive: propTypes.exports.string,
  exit: propTypes.exports.string,
  exitDone: propTypes.exports.string,
  exitActive: propTypes.exports.string
})]) ;

var TransitionGroupContext = React__default.createContext(null);

var forceReflow = function forceReflow(node) {
  return node.scrollTop;
};

var UNMOUNTED = 'unmounted';
var EXITED = 'exited';
var ENTERING = 'entering';
var ENTERED = 'entered';
var EXITING = 'exiting';
/**
 * The Transition component lets you describe a transition from one component
 * state to another _over time_ with a simple declarative API. Most commonly
 * it's used to animate the mounting and unmounting of a component, but can also
 * be used to describe in-place transition states as well.
 *
 * ---
 *
 * **Note**: `Transition` is a platform-agnostic base component. If you're using
 * transitions in CSS, you'll probably want to use
 * [`CSSTransition`](https://reactcommunity.org/react-transition-group/css-transition)
 * instead. It inherits all the features of `Transition`, but contains
 * additional features necessary to play nice with CSS transitions (hence the
 * name of the component).
 *
 * ---
 *
 * By default the `Transition` component does not alter the behavior of the
 * component it renders, it only tracks "enter" and "exit" states for the
 * components. It's up to you to give meaning and effect to those states. For
 * example we can add styles to a component when it enters or exits:
 *
 * ```jsx
 * import { Transition } from 'react-transition-group';
 *
 * const duration = 300;
 *
 * const defaultStyle = {
 *   transition: `opacity ${duration}ms ease-in-out`,
 *   opacity: 0,
 * }
 *
 * const transitionStyles = {
 *   entering: { opacity: 1 },
 *   entered:  { opacity: 1 },
 *   exiting:  { opacity: 0 },
 *   exited:  { opacity: 0 },
 * };
 *
 * const Fade = ({ in: inProp }) => (
 *   <Transition in={inProp} timeout={duration}>
 *     {state => (
 *       <div style={{
 *         ...defaultStyle,
 *         ...transitionStyles[state]
 *       }}>
 *         I'm a fade Transition!
 *       </div>
 *     )}
 *   </Transition>
 * );
 * ```
 *
 * There are 4 main states a Transition can be in:
 *  - `'entering'`
 *  - `'entered'`
 *  - `'exiting'`
 *  - `'exited'`
 *
 * Transition state is toggled via the `in` prop. When `true` the component
 * begins the "Enter" stage. During this stage, the component will shift from
 * its current transition state, to `'entering'` for the duration of the
 * transition and then to the `'entered'` stage once it's complete. Let's take
 * the following example (we'll use the
 * [useState](https://reactjs.org/docs/hooks-reference.html#usestate) hook):
 *
 * ```jsx
 * function App() {
 *   const [inProp, setInProp] = useState(false);
 *   return (
 *     <div>
 *       <Transition in={inProp} timeout={500}>
 *         {state => (
 *           // ...
 *         )}
 *       </Transition>
 *       <button onClick={() => setInProp(true)}>
 *         Click to Enter
 *       </button>
 *     </div>
 *   );
 * }
 * ```
 *
 * When the button is clicked the component will shift to the `'entering'` state
 * and stay there for 500ms (the value of `timeout`) before it finally switches
 * to `'entered'`.
 *
 * When `in` is `false` the same thing happens except the state moves from
 * `'exiting'` to `'exited'`.
 */

var Transition = /*#__PURE__*/function (_React$Component) {
  _inheritsLoose(Transition, _React$Component);
  function Transition(props, context) {
    var _this;
    _this = _React$Component.call(this, props, context) || this;
    var parentGroup = context; // In the context of a TransitionGroup all enters are really appears

    var appear = parentGroup && !parentGroup.isMounting ? props.enter : props.appear;
    var initialStatus;
    _this.appearStatus = null;
    if (props.in) {
      if (appear) {
        initialStatus = EXITED;
        _this.appearStatus = ENTERING;
      } else {
        initialStatus = ENTERED;
      }
    } else {
      if (props.unmountOnExit || props.mountOnEnter) {
        initialStatus = UNMOUNTED;
      } else {
        initialStatus = EXITED;
      }
    }
    _this.state = {
      status: initialStatus
    };
    _this.nextCallback = null;
    return _this;
  }
  Transition.getDerivedStateFromProps = function getDerivedStateFromProps(_ref, prevState) {
    var nextIn = _ref.in;
    if (nextIn && prevState.status === UNMOUNTED) {
      return {
        status: EXITED
      };
    }
    return null;
  } // getSnapshotBeforeUpdate(prevProps) {
  //   let nextStatus = null
  //   if (prevProps !== this.props) {
  //     const { status } = this.state
  //     if (this.props.in) {
  //       if (status !== ENTERING && status !== ENTERED) {
  //         nextStatus = ENTERING
  //       }
  //     } else {
  //       if (status === ENTERING || status === ENTERED) {
  //         nextStatus = EXITING
  //       }
  //     }
  //   }
  //   return { nextStatus }
  // }
  ;

  var _proto = Transition.prototype;
  _proto.componentDidMount = function componentDidMount() {
    this.updateStatus(true, this.appearStatus);
  };
  _proto.componentDidUpdate = function componentDidUpdate(prevProps) {
    var nextStatus = null;
    if (prevProps !== this.props) {
      var status = this.state.status;
      if (this.props.in) {
        if (status !== ENTERING && status !== ENTERED) {
          nextStatus = ENTERING;
        }
      } else {
        if (status === ENTERING || status === ENTERED) {
          nextStatus = EXITING;
        }
      }
    }
    this.updateStatus(false, nextStatus);
  };
  _proto.componentWillUnmount = function componentWillUnmount() {
    this.cancelNextCallback();
  };
  _proto.getTimeouts = function getTimeouts() {
    var timeout = this.props.timeout;
    var exit, enter, appear;
    exit = enter = appear = timeout;
    if (timeout != null && typeof timeout !== 'number') {
      exit = timeout.exit;
      enter = timeout.enter; // TODO: remove fallback for next major

      appear = timeout.appear !== undefined ? timeout.appear : enter;
    }
    return {
      exit: exit,
      enter: enter,
      appear: appear
    };
  };
  _proto.updateStatus = function updateStatus(mounting, nextStatus) {
    if (mounting === void 0) {
      mounting = false;
    }
    if (nextStatus !== null) {
      // nextStatus will always be ENTERING or EXITING.
      this.cancelNextCallback();
      if (nextStatus === ENTERING) {
        if (this.props.unmountOnExit || this.props.mountOnEnter) {
          var node = this.props.nodeRef ? this.props.nodeRef.current : ReactDOM.findDOMNode(this); // https://github.com/reactjs/react-transition-group/pull/749
          // With unmountOnExit or mountOnEnter, the enter animation should happen at the transition between `exited` and `entering`.
          // To make the animation happen,  we have to separate each rendering and avoid being processed as batched.

          if (node) forceReflow(node);
        }
        this.performEnter(mounting);
      } else {
        this.performExit();
      }
    } else if (this.props.unmountOnExit && this.state.status === EXITED) {
      this.setState({
        status: UNMOUNTED
      });
    }
  };
  _proto.performEnter = function performEnter(mounting) {
    var _this2 = this;
    var enter = this.props.enter;
    var appearing = this.context ? this.context.isMounting : mounting;
    var _ref2 = this.props.nodeRef ? [appearing] : [ReactDOM.findDOMNode(this), appearing],
      maybeNode = _ref2[0],
      maybeAppearing = _ref2[1];
    var timeouts = this.getTimeouts();
    var enterTimeout = appearing ? timeouts.appear : timeouts.enter; // no enter animation skip right to ENTERED
    // if we are mounting and running this it means appear _must_ be set

    if (!mounting && !enter || config.disabled) {
      this.safeSetState({
        status: ENTERED
      }, function () {
        _this2.props.onEntered(maybeNode);
      });
      return;
    }
    this.props.onEnter(maybeNode, maybeAppearing);
    this.safeSetState({
      status: ENTERING
    }, function () {
      _this2.props.onEntering(maybeNode, maybeAppearing);
      _this2.onTransitionEnd(enterTimeout, function () {
        _this2.safeSetState({
          status: ENTERED
        }, function () {
          _this2.props.onEntered(maybeNode, maybeAppearing);
        });
      });
    });
  };
  _proto.performExit = function performExit() {
    var _this3 = this;
    var exit = this.props.exit;
    var timeouts = this.getTimeouts();
    var maybeNode = this.props.nodeRef ? undefined : ReactDOM.findDOMNode(this); // no exit animation skip right to EXITED

    if (!exit || config.disabled) {
      this.safeSetState({
        status: EXITED
      }, function () {
        _this3.props.onExited(maybeNode);
      });
      return;
    }
    this.props.onExit(maybeNode);
    this.safeSetState({
      status: EXITING
    }, function () {
      _this3.props.onExiting(maybeNode);
      _this3.onTransitionEnd(timeouts.exit, function () {
        _this3.safeSetState({
          status: EXITED
        }, function () {
          _this3.props.onExited(maybeNode);
        });
      });
    });
  };
  _proto.cancelNextCallback = function cancelNextCallback() {
    if (this.nextCallback !== null) {
      this.nextCallback.cancel();
      this.nextCallback = null;
    }
  };
  _proto.safeSetState = function safeSetState(nextState, callback) {
    // This shouldn't be necessary, but there are weird race conditions with
    // setState callbacks and unmounting in testing, so always make sure that
    // we can cancel any pending setState callbacks after we unmount.
    callback = this.setNextCallback(callback);
    this.setState(nextState, callback);
  };
  _proto.setNextCallback = function setNextCallback(callback) {
    var _this4 = this;
    var active = true;
    this.nextCallback = function (event) {
      if (active) {
        active = false;
        _this4.nextCallback = null;
        callback(event);
      }
    };
    this.nextCallback.cancel = function () {
      active = false;
    };
    return this.nextCallback;
  };
  _proto.onTransitionEnd = function onTransitionEnd(timeout, handler) {
    this.setNextCallback(handler);
    var node = this.props.nodeRef ? this.props.nodeRef.current : ReactDOM.findDOMNode(this);
    var doesNotHaveTimeoutOrListener = timeout == null && !this.props.addEndListener;
    if (!node || doesNotHaveTimeoutOrListener) {
      setTimeout(this.nextCallback, 0);
      return;
    }
    if (this.props.addEndListener) {
      var _ref3 = this.props.nodeRef ? [this.nextCallback] : [node, this.nextCallback],
        maybeNode = _ref3[0],
        maybeNextCallback = _ref3[1];
      this.props.addEndListener(maybeNode, maybeNextCallback);
    }
    if (timeout != null) {
      setTimeout(this.nextCallback, timeout);
    }
  };
  _proto.render = function render() {
    var status = this.state.status;
    if (status === UNMOUNTED) {
      return null;
    }
    var _this$props = this.props,
      children = _this$props.children;
      _this$props.in;
      _this$props.mountOnEnter;
      _this$props.unmountOnExit;
      _this$props.appear;
      _this$props.enter;
      _this$props.exit;
      _this$props.timeout;
      _this$props.addEndListener;
      _this$props.onEnter;
      _this$props.onEntering;
      _this$props.onEntered;
      _this$props.onExit;
      _this$props.onExiting;
      _this$props.onExited;
      _this$props.nodeRef;
      var childProps = _objectWithoutPropertiesLoose(_this$props, ["children", "in", "mountOnEnter", "unmountOnExit", "appear", "enter", "exit", "timeout", "addEndListener", "onEnter", "onEntering", "onEntered", "onExit", "onExiting", "onExited", "nodeRef"]);
    return /*#__PURE__*/(
      // allows for nested Transitions
      React__default.createElement(TransitionGroupContext.Provider, {
        value: null
      }, typeof children === 'function' ? children(status, childProps) : React__default.cloneElement(React__default.Children.only(children), childProps))
    );
  };
  return Transition;
}(React__default.Component);
Transition.contextType = TransitionGroupContext;
Transition.propTypes = {
  /**
   * A React reference to DOM element that need to transition:
   * https://stackoverflow.com/a/51127130/4671932
   *
   *   - When `nodeRef` prop is used, `node` is not passed to callback functions
   *      (e.g. `onEnter`) because user already has direct access to the node.
   *   - When changing `key` prop of `Transition` in a `TransitionGroup` a new
   *     `nodeRef` need to be provided to `Transition` with changed `key` prop
   *     (see
   *     [test/CSSTransition-test.js](https://github.com/reactjs/react-transition-group/blob/13435f897b3ab71f6e19d724f145596f5910581c/test/CSSTransition-test.js#L362-L437)).
   */
  nodeRef: propTypes.exports.shape({
    current: typeof Element === 'undefined' ? propTypes.exports.any : function (propValue, key, componentName, location, propFullName, secret) {
      var value = propValue[key];
      return propTypes.exports.instanceOf(value && 'ownerDocument' in value ? value.ownerDocument.defaultView.Element : Element)(propValue, key, componentName, location, propFullName, secret);
    }
  }),
  /**
   * A `function` child can be used instead of a React element. This function is
   * called with the current transition status (`'entering'`, `'entered'`,
   * `'exiting'`, `'exited'`), which can be used to apply context
   * specific props to a component.
   *
   * ```jsx
   * <Transition in={this.state.in} timeout={150}>
   *   {state => (
   *     <MyComponent className={`fade fade-${state}`} />
   *   )}
   * </Transition>
   * ```
   */
  children: propTypes.exports.oneOfType([propTypes.exports.func.isRequired, propTypes.exports.element.isRequired]).isRequired,
  /**
   * Show the component; triggers the enter or exit states
   */
  in: propTypes.exports.bool,
  /**
   * By default the child component is mounted immediately along with
   * the parent `Transition` component. If you want to "lazy mount" the component on the
   * first `in={true}` you can set `mountOnEnter`. After the first enter transition the component will stay
   * mounted, even on "exited", unless you also specify `unmountOnExit`.
   */
  mountOnEnter: propTypes.exports.bool,
  /**
   * By default the child component stays mounted after it reaches the `'exited'` state.
   * Set `unmountOnExit` if you'd prefer to unmount the component after it finishes exiting.
   */
  unmountOnExit: propTypes.exports.bool,
  /**
   * By default the child component does not perform the enter transition when
   * it first mounts, regardless of the value of `in`. If you want this
   * behavior, set both `appear` and `in` to `true`.
   *
   * > **Note**: there are no special appear states like `appearing`/`appeared`, this prop
   * > only adds an additional enter transition. However, in the
   * > `<CSSTransition>` component that first enter transition does result in
   * > additional `.appear-*` classes, that way you can choose to style it
   * > differently.
   */
  appear: propTypes.exports.bool,
  /**
   * Enable or disable enter transitions.
   */
  enter: propTypes.exports.bool,
  /**
   * Enable or disable exit transitions.
   */
  exit: propTypes.exports.bool,
  /**
   * The duration of the transition, in milliseconds.
   * Required unless `addEndListener` is provided.
   *
   * You may specify a single timeout for all transitions:
   *
   * ```jsx
   * timeout={500}
   * ```
   *
   * or individually:
   *
   * ```jsx
   * timeout={{
   *  appear: 500,
   *  enter: 300,
   *  exit: 500,
   * }}
   * ```
   *
   * - `appear` defaults to the value of `enter`
   * - `enter` defaults to `0`
   * - `exit` defaults to `0`
   *
   * @type {number | { enter?: number, exit?: number, appear?: number }}
   */
  timeout: function timeout(props) {
    var pt = timeoutsShape;
    if (!props.addEndListener) pt = pt.isRequired;
    for (var _len = arguments.length, args = new Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
      args[_key - 1] = arguments[_key];
    }
    return pt.apply(void 0, [props].concat(args));
  },
  /**
   * Add a custom transition end trigger. Called with the transitioning
   * DOM node and a `done` callback. Allows for more fine grained transition end
   * logic. Timeouts are still used as a fallback if provided.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * ```jsx
   * addEndListener={(node, done) => {
   *   // use the css transitionend event to mark the finish of a transition
   *   node.addEventListener('transitionend', done, false);
   * }}
   * ```
   */
  addEndListener: propTypes.exports.func,
  /**
   * Callback fired before the "entering" status is applied. An extra parameter
   * `isAppearing` is supplied to indicate if the enter stage is occurring on the initial mount
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement, isAppearing: bool) -> void
   */
  onEnter: propTypes.exports.func,
  /**
   * Callback fired after the "entering" status is applied. An extra parameter
   * `isAppearing` is supplied to indicate if the enter stage is occurring on the initial mount
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement, isAppearing: bool)
   */
  onEntering: propTypes.exports.func,
  /**
   * Callback fired after the "entered" status is applied. An extra parameter
   * `isAppearing` is supplied to indicate if the enter stage is occurring on the initial mount
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement, isAppearing: bool) -> void
   */
  onEntered: propTypes.exports.func,
  /**
   * Callback fired before the "exiting" status is applied.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement) -> void
   */
  onExit: propTypes.exports.func,
  /**
   * Callback fired after the "exiting" status is applied.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement) -> void
   */
  onExiting: propTypes.exports.func,
  /**
   * Callback fired after the "exited" status is applied.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed
   *
   * @type Function(node: HtmlElement) -> void
   */
  onExited: propTypes.exports.func
} ; // Name the function so it is clearer in the documentation

function noop() {}
Transition.defaultProps = {
  in: false,
  mountOnEnter: false,
  unmountOnExit: false,
  appear: false,
  enter: true,
  exit: true,
  onEnter: noop,
  onEntering: noop,
  onEntered: noop,
  onExit: noop,
  onExiting: noop,
  onExited: noop
};
Transition.UNMOUNTED = UNMOUNTED;
Transition.EXITED = EXITED;
Transition.ENTERING = ENTERING;
Transition.ENTERED = ENTERED;
Transition.EXITING = EXITING;

var canUseDOM = !!(typeof window !== 'undefined' && window.document && window.document.createElement);

/* eslint-disable no-return-assign */
var optionsSupported = false;
var onceSupported = false;
try {
  var options = {
    get passive() {
      return optionsSupported = true;
    },
    get once() {
      // eslint-disable-next-line no-multi-assign
      return onceSupported = optionsSupported = true;
    }
  };
  if (canUseDOM) {
    window.addEventListener('test', options, options);
    window.removeEventListener('test', options, true);
  }
} catch (e) {
  /* */
}

/**
 * An `addEventListener` ponyfill, supports the `once` option
 * 
 * @param node the element
 * @param eventName the event name
 * @param handle the handler
 * @param options event options
 */
function addEventListener(node, eventName, handler, options) {
  if (options && typeof options !== 'boolean' && !onceSupported) {
    var once = options.once,
      capture = options.capture;
    var wrappedHandler = handler;
    if (!onceSupported && once) {
      wrappedHandler = handler.__once || function onceHandler(event) {
        this.removeEventListener(eventName, onceHandler, capture);
        handler.call(this, event);
      };
      handler.__once = wrappedHandler;
    }
    node.addEventListener(eventName, wrappedHandler, optionsSupported ? options : capture);
  }
  node.addEventListener(eventName, handler, options);
}

/**
 * A `removeEventListener` ponyfill
 * 
 * @param node the element
 * @param eventName the event name
 * @param handle the handler
 * @param options event options
 */
function removeEventListener(node, eventName, handler, options) {
  var capture = options && typeof options !== 'boolean' ? options.capture : options;
  node.removeEventListener(eventName, handler, capture);
  if (handler.__once) {
    node.removeEventListener(eventName, handler.__once, capture);
  }
}

function listen(node, eventName, handler, options) {
  addEventListener(node, eventName, handler, options);
  return function () {
    removeEventListener(node, eventName, handler, options);
  };
}

/**
 * Triggers an event on a given element.
 * 
 * @param node the element
 * @param eventName the event name to trigger
 * @param bubbles whether the event should bubble up
 * @param cancelable whether the event should be cancelable
 */
function triggerEvent(node, eventName, bubbles, cancelable) {
  if (bubbles === void 0) {
    bubbles = false;
  }
  if (cancelable === void 0) {
    cancelable = true;
  }
  if (node) {
    var event = document.createEvent('HTMLEvents');
    event.initEvent(eventName, bubbles, cancelable);
    node.dispatchEvent(event);
  }
}

function parseDuration$1(node) {
  var str = style(node, 'transitionDuration') || '';
  var mult = str.indexOf('ms') === -1 ? 1000 : 1;
  return parseFloat(str) * mult;
}
function emulateTransitionEnd(element, duration, padding) {
  if (padding === void 0) {
    padding = 5;
  }
  var called = false;
  var handle = setTimeout(function () {
    if (!called) triggerEvent(element, 'transitionend', true);
  }, duration + padding);
  var remove = listen(element, 'transitionend', function () {
    called = true;
  }, {
    once: true
  });
  return function () {
    clearTimeout(handle);
    remove();
  };
}
function transitionEnd(element, handler, duration, padding) {
  if (duration == null) duration = parseDuration$1(element) || 0;
  var removeEmulate = emulateTransitionEnd(element, duration, padding);
  var remove = listen(element, 'transitionend', handler);
  return function () {
    removeEmulate();
    remove();
  };
}

function parseDuration(node, property) {
  const str = style(node, property) || '';
  const mult = str.indexOf('ms') === -1 ? 1000 : 1;
  return parseFloat(str) * mult;
}
function transitionEndListener(element, handler) {
  const duration = parseDuration(element, 'transitionDuration');
  const delay = parseDuration(element, 'transitionDelay');
  const remove = transitionEnd(element, e => {
    if (e.target === element) {
      remove();
      handler(e);
    }
  }, duration + delay);
}

/**
 * Safe chained function
 *
 * Will only create a new function if needed,
 * otherwise will pass back existing functions or null.
 *
 * @param {function} functions to chain
 * @returns {function|null}
 */
function createChainedFunction(...funcs) {
  return funcs.filter(f => f != null).reduce((acc, f) => {
    if (typeof f !== 'function') {
      throw new Error('Invalid Argument Type, must only provide functions, undefined, or null.');
    }
    if (acc === null) return f;
    return function chainedFunction(...args) {
      // @ts-ignore
      acc.apply(this, args);
      // @ts-ignore
      f.apply(this, args);
    };
  }, null);
}

// reading a dimension prop will cause the browser to recalculate,
// which will let our animations work
function triggerBrowserReflow(node) {
  // eslint-disable-next-line @typescript-eslint/no-unused-expressions
  node.offsetHeight;
}

var toFnRef = function toFnRef(ref) {
  return !ref || typeof ref === 'function' ? ref : function (value) {
    ref.current = value;
  };
};
function mergeRefs(refA, refB) {
  var a = toFnRef(refA);
  var b = toFnRef(refB);
  return function (value) {
    if (a) a(value);
    if (b) b(value);
  };
}
/**
 * Create and returns a single callback ref composed from two other Refs.
 *
 * ```tsx
 * const Button = React.forwardRef((props, ref) => {
 *   const [element, attachRef] = useCallbackRef<HTMLButtonElement>();
 *   const mergedRef = useMergedRefs(ref, attachRef);
 *
 *   return <button ref={mergedRef} {...props}/>
 * })
 * ```
 *
 * @param refA A Callback or mutable Ref
 * @param refB A Callback or mutable Ref
 * @category refs
 */

function useMergedRefs(refA, refB) {
  return useMemo(function () {
    return mergeRefs(refA, refB);
  }, [refA, refB]);
}

function safeFindDOMNode(componentOrElement) {
  if (componentOrElement && 'setState' in componentOrElement) {
    return ReactDOM.findDOMNode(componentOrElement);
  }
  return componentOrElement != null ? componentOrElement : null;
}

// Normalizes Transition callbacks when nodeRef is used.
const TransitionWrapper = /*#__PURE__*/React__default.forwardRef(({
  onEnter,
  onEntering,
  onEntered,
  onExit,
  onExiting,
  onExited,
  addEndListener,
  children,
  childRef,
  ...props
}, ref) => {
  const nodeRef = useRef(null);
  const mergedRef = useMergedRefs(nodeRef, childRef);
  const attachRef = r => {
    mergedRef(safeFindDOMNode(r));
  };
  const normalize = callback => param => {
    if (callback && nodeRef.current) {
      callback(nodeRef.current, param);
    }
  };

  /* eslint-disable react-hooks/exhaustive-deps */
  const handleEnter = useCallback(normalize(onEnter), [onEnter]);
  const handleEntering = useCallback(normalize(onEntering), [onEntering]);
  const handleEntered = useCallback(normalize(onEntered), [onEntered]);
  const handleExit = useCallback(normalize(onExit), [onExit]);
  const handleExiting = useCallback(normalize(onExiting), [onExiting]);
  const handleExited = useCallback(normalize(onExited), [onExited]);
  const handleAddEndListener = useCallback(normalize(addEndListener), [addEndListener]);
  /* eslint-enable react-hooks/exhaustive-deps */

  return /*#__PURE__*/jsx(Transition, {
    ref: ref,
    ...props,
    onEnter: handleEnter,
    onEntered: handleEntered,
    onEntering: handleEntering,
    onExit: handleExit,
    onExited: handleExited,
    onExiting: handleExiting,
    addEndListener: handleAddEndListener,
    nodeRef: nodeRef,
    children: typeof children === 'function' ? (status, innerProps) => children(status, {
      ...innerProps,
      ref: attachRef
    }) : /*#__PURE__*/React__default.cloneElement(children, {
      ref: attachRef
    })
  });
});

const MARGINS = {
  height: ['marginTop', 'marginBottom'],
  width: ['marginLeft', 'marginRight']
};
function getDefaultDimensionValue(dimension, elem) {
  const offset = `offset${dimension[0].toUpperCase()}${dimension.slice(1)}`;
  const value = elem[offset];
  const margins = MARGINS[dimension];
  return value +
  // @ts-ignore
  parseInt(style(elem, margins[0]), 10) +
  // @ts-ignore
  parseInt(style(elem, margins[1]), 10);
}
const collapseStyles = {
  [EXITED]: 'collapse',
  [EXITING]: 'collapsing',
  [ENTERING]: 'collapsing',
  [ENTERED]: 'collapse show'
};
const defaultProps = {
  in: false,
  timeout: 300,
  mountOnEnter: false,
  unmountOnExit: false,
  appear: false,
  getDimensionValue: getDefaultDimensionValue
};
const Collapse = /*#__PURE__*/React__default.forwardRef(({
  onEnter,
  onEntering,
  onEntered,
  onExit,
  onExiting,
  className,
  children,
  dimension = 'height',
  getDimensionValue = getDefaultDimensionValue,
  ...props
}, ref) => {
  /* Compute dimension */
  const computedDimension = typeof dimension === 'function' ? dimension() : dimension;

  /* -- Expanding -- */
  const handleEnter = useMemo(() => createChainedFunction(elem => {
    elem.style[computedDimension] = '0';
  }, onEnter), [computedDimension, onEnter]);
  const handleEntering = useMemo(() => createChainedFunction(elem => {
    const scroll = `scroll${computedDimension[0].toUpperCase()}${computedDimension.slice(1)}`;
    elem.style[computedDimension] = `${elem[scroll]}px`;
  }, onEntering), [computedDimension, onEntering]);
  const handleEntered = useMemo(() => createChainedFunction(elem => {
    elem.style[computedDimension] = null;
  }, onEntered), [computedDimension, onEntered]);

  /* -- Collapsing -- */
  const handleExit = useMemo(() => createChainedFunction(elem => {
    elem.style[computedDimension] = `${getDimensionValue(computedDimension, elem)}px`;
    triggerBrowserReflow(elem);
  }, onExit), [onExit, getDimensionValue, computedDimension]);
  const handleExiting = useMemo(() => createChainedFunction(elem => {
    elem.style[computedDimension] = null;
  }, onExiting), [computedDimension, onExiting]);
  return /*#__PURE__*/jsx(TransitionWrapper, {
    ref: ref,
    addEndListener: transitionEndListener,
    ...props,
    "aria-expanded": props.role ? props.in : null,
    onEnter: handleEnter,
    onEntering: handleEntering,
    onEntered: handleEntered,
    onExit: handleExit,
    onExiting: handleExiting,
    childRef: children.ref,
    children: (state, innerProps) => /*#__PURE__*/React__default.cloneElement(children, {
      ...innerProps,
      className: classNames(className, children.props.className, collapseStyles[state], computedDimension === 'width' && 'collapse-horizontal')
    })
  });
});

// @ts-ignore

// @ts-ignore
Collapse.defaultProps = defaultProps;

function isAccordionItemSelected(activeEventKey, eventKey) {
  return Array.isArray(activeEventKey) ? activeEventKey.includes(eventKey) : activeEventKey === eventKey;
}
const context$1 = /*#__PURE__*/React.createContext({});
context$1.displayName = 'AccordionContext';

/**
 * This component accepts all of [`Collapse`'s props](/utilities/transitions/#collapse-props).
 */
const AccordionCollapse = /*#__PURE__*/React.forwardRef(({
  as: Component = 'div',
  bsPrefix,
  className,
  children,
  eventKey,
  ...props
}, ref) => {
  const {
    activeEventKey
  } = useContext(context$1);
  bsPrefix = useBootstrapPrefix(bsPrefix, 'accordion-collapse');
  return /*#__PURE__*/jsx(Collapse, {
    ref: ref,
    in: isAccordionItemSelected(activeEventKey, eventKey),
    ...props,
    className: classNames(className, bsPrefix),
    children: /*#__PURE__*/jsx(Component, {
      children: React.Children.only(children)
    })
  });
});
AccordionCollapse.displayName = 'AccordionCollapse';

const context = /*#__PURE__*/React.createContext({
  eventKey: ''
});
context.displayName = 'AccordionItemContext';

const AccordionBody = /*#__PURE__*/React.forwardRef(({
  // Need to define the default "as" during prop destructuring to be compatible with styled-components github.com/react-bootstrap/react-bootstrap/issues/3595
  as: Component = 'div',
  bsPrefix,
  className,
  onEnter,
  onEntering,
  onEntered,
  onExit,
  onExiting,
  onExited,
  ...props
}, ref) => {
  bsPrefix = useBootstrapPrefix(bsPrefix, 'accordion-body');
  const {
    eventKey
  } = useContext(context);
  return /*#__PURE__*/jsx(AccordionCollapse, {
    eventKey: eventKey,
    onEnter: onEnter,
    onEntering: onEntering,
    onEntered: onEntered,
    onExit: onExit,
    onExiting: onExiting,
    onExited: onExited,
    children: /*#__PURE__*/jsx(Component, {
      ref: ref,
      ...props,
      className: classNames(className, bsPrefix)
    })
  });
});
AccordionBody.displayName = 'AccordionBody';

function useAccordionButton(eventKey, onClick) {
  const {
    activeEventKey,
    onSelect,
    alwaysOpen
  } = useContext(context$1);
  return e => {
    /*
      Compare the event key in context with the given event key.
      If they are the same, then collapse the component.
    */
    let eventKeyPassed = eventKey === activeEventKey ? null : eventKey;
    if (alwaysOpen) {
      if (Array.isArray(activeEventKey)) {
        if (activeEventKey.includes(eventKey)) {
          eventKeyPassed = activeEventKey.filter(k => k !== eventKey);
        } else {
          eventKeyPassed = [...activeEventKey, eventKey];
        }
      } else {
        // activeEventKey is undefined.
        eventKeyPassed = [eventKey];
      }
    }
    onSelect == null ? void 0 : onSelect(eventKeyPassed, e);
    onClick == null ? void 0 : onClick(e);
  };
}
const AccordionButton = /*#__PURE__*/React.forwardRef(({
  // Need to define the default "as" during prop destructuring to be compatible with styled-components github.com/react-bootstrap/react-bootstrap/issues/3595
  as: Component = 'button',
  bsPrefix,
  className,
  onClick,
  ...props
}, ref) => {
  bsPrefix = useBootstrapPrefix(bsPrefix, 'accordion-button');
  const {
    eventKey
  } = useContext(context);
  const accordionOnClick = useAccordionButton(eventKey, onClick);
  const {
    activeEventKey
  } = useContext(context$1);
  if (Component === 'button') {
    props.type = 'button';
  }
  return /*#__PURE__*/jsx(Component, {
    ref: ref,
    onClick: accordionOnClick,
    ...props,
    "aria-expanded": eventKey === activeEventKey,
    className: classNames(className, bsPrefix, !isAccordionItemSelected(activeEventKey, eventKey) && 'collapsed')
  });
});
AccordionButton.displayName = 'AccordionButton';

const AccordionHeader = /*#__PURE__*/React.forwardRef(({
  // Need to define the default "as" during prop destructuring to be compatible with styled-components github.com/react-bootstrap/react-bootstrap/issues/3595
  as: Component = 'h2',
  bsPrefix,
  className,
  children,
  onClick,
  ...props
}, ref) => {
  bsPrefix = useBootstrapPrefix(bsPrefix, 'accordion-header');
  return /*#__PURE__*/jsx(Component, {
    ref: ref,
    ...props,
    className: classNames(className, bsPrefix),
    children: /*#__PURE__*/jsx(AccordionButton, {
      onClick: onClick,
      children: children
    })
  });
});
AccordionHeader.displayName = 'AccordionHeader';

const AccordionItem = /*#__PURE__*/React.forwardRef(({
  // Need to define the default "as" during prop destructuring to be compatible with styled-components github.com/react-bootstrap/react-bootstrap/issues/3595
  as: Component = 'div',
  bsPrefix,
  className,
  eventKey,
  ...props
}, ref) => {
  bsPrefix = useBootstrapPrefix(bsPrefix, 'accordion-item');
  const contextValue = useMemo(() => ({
    eventKey
  }), [eventKey]);
  return /*#__PURE__*/jsx(context.Provider, {
    value: contextValue,
    children: /*#__PURE__*/jsx(Component, {
      ref: ref,
      ...props,
      className: classNames(className, bsPrefix)
    })
  });
});
AccordionItem.displayName = 'AccordionItem';

const Accordion = /*#__PURE__*/React.forwardRef((props, ref) => {
  const {
    // Need to define the default "as" during prop destructuring to be compatible with styled-components github.com/react-bootstrap/react-bootstrap/issues/3595
    as: Component = 'div',
    activeKey,
    bsPrefix,
    className,
    onSelect,
    flush,
    alwaysOpen,
    ...controlledProps
  } = useUncontrolled(props, {
    activeKey: 'onSelect'
  });
  const prefix = useBootstrapPrefix(bsPrefix, 'accordion');
  const contextValue = useMemo(() => ({
    activeEventKey: activeKey,
    onSelect,
    alwaysOpen
  }), [activeKey, onSelect, alwaysOpen]);
  return /*#__PURE__*/jsx(context$1.Provider, {
    value: contextValue,
    children: /*#__PURE__*/jsx(Component, {
      ref: ref,
      ...controlledProps,
      className: classNames(className, prefix, flush && `${prefix}-flush`)
    })
  });
});
Accordion.displayName = 'Accordion';
var Accordion$1 = Object.assign(Accordion, {
  Button: AccordionButton,
  Collapse: AccordionCollapse,
  Item: AccordionItem,
  Header: AccordionHeader,
  Body: AccordionBody
});

class Accordian extends Component {
    constructor() {
        var _a, _b;
        super(...arguments);
        this.header = ((_a = this.props.heading) === null || _a === void 0 ? void 0 : _a.value) ? (_b = this.props.heading) === null || _b === void 0 ? void 0 : _b.value : " ";
        this.handleEnter = () => {
            if (this.props.onEnter && this.props.onEnter.canExecute) {
                this.props.onEnter.execute();
            }
        };
        this.handleExit = () => {
            if (this.props.onExit && this.props.onExit.canExecute) {
                this.props.onExit.execute();
            }
        };
        this.handler = () => {
            if (this.props.boolean) {
                if (this.props.onEnter && this.props.onEnter.canExecute) {
                    this.props.onEnter.execute();
                }
                return "0";
            }
            else {
                return "";
            }
        };
        this.handledefaultopen = this.handler;
    }
    render() {
        var _a, _b;
        this.header = ((_a = this.props.heading) === null || _a === void 0 ? void 0 : _a.value) ? (_b = this.props.heading) === null || _b === void 0 ? void 0 : _b.value : " ";
        return (createElement(Accordion$1, { defaultActiveKey: this.handledefaultopen },
            createElement(Accordion$1.Item, { eventKey: "0" },
                createElement(Accordion$1.Header, { className: "AccordianHeader" }, this.header),
                createElement(Accordion$1.Body, { onEnter: this.handleEnter, onExit: this.handleExit }, this.props.content))));
    }
}

export { Accordian };
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiQWNjb3JkaWFuLm1qcyIsInNvdXJjZXMiOlsiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL2NsYXNzbmFtZXMvaW5kZXguanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvQGJhYmVsL3J1bnRpbWUvaGVscGVycy9lc20vZXh0ZW5kcy5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9AYmFiZWwvcnVudGltZS9oZWxwZXJzL2VzbS9vYmplY3RXaXRob3V0UHJvcGVydGllc0xvb3NlLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3VuY29udHJvbGxhYmxlL2xpYi9lc20vdXRpbHMuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvdW5jb250cm9sbGFibGUvbGliL2VzbS9ob29rLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL0BiYWJlbC9ydW50aW1lL2hlbHBlcnMvZXNtL3NldFByb3RvdHlwZU9mLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL0BiYWJlbC9ydW50aW1lL2hlbHBlcnMvZXNtL2luaGVyaXRzTG9vc2UuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS9UaGVtZVByb3ZpZGVyLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL2RvbS1oZWxwZXJzL2VzbS9vd25lckRvY3VtZW50LmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL2RvbS1oZWxwZXJzL2VzbS9vd25lcldpbmRvdy5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9kb20taGVscGVycy9lc20vZ2V0Q29tcHV0ZWRTdHlsZS5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9kb20taGVscGVycy9lc20vaHlwaGVuYXRlLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL2RvbS1oZWxwZXJzL2VzbS9oeXBoZW5hdGVTdHlsZS5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9kb20taGVscGVycy9lc20vaXNUcmFuc2Zvcm0uanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvZG9tLWhlbHBlcnMvZXNtL2Nzcy5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9wcm9wLXR5cGVzL25vZGVfbW9kdWxlcy9yZWFjdC1pcy9janMvcmVhY3QtaXMuZGV2ZWxvcG1lbnQuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcHJvcC10eXBlcy9ub2RlX21vZHVsZXMvcmVhY3QtaXMvaW5kZXguanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvb2JqZWN0LWFzc2lnbi9pbmRleC5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9wcm9wLXR5cGVzL2xpYi9SZWFjdFByb3BUeXBlc1NlY3JldC5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9wcm9wLXR5cGVzL2xpYi9oYXMuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcHJvcC10eXBlcy9jaGVja1Byb3BUeXBlcy5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9wcm9wLXR5cGVzL2ZhY3RvcnlXaXRoVHlwZUNoZWNrZXJzLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3Byb3AtdHlwZXMvaW5kZXguanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtdHJhbnNpdGlvbi1ncm91cC9lc20vY29uZmlnLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvZXNtL3V0aWxzL1Byb3BUeXBlcy5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9yZWFjdC10cmFuc2l0aW9uLWdyb3VwL2VzbS9UcmFuc2l0aW9uR3JvdXBDb250ZXh0LmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvZXNtL3V0aWxzL3JlZmxvdy5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9yZWFjdC10cmFuc2l0aW9uLWdyb3VwL2VzbS9UcmFuc2l0aW9uLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL2RvbS1oZWxwZXJzL2VzbS9jYW5Vc2VET00uanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvZG9tLWhlbHBlcnMvZXNtL2FkZEV2ZW50TGlzdGVuZXIuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvZG9tLWhlbHBlcnMvZXNtL3JlbW92ZUV2ZW50TGlzdGVuZXIuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvZG9tLWhlbHBlcnMvZXNtL2xpc3Rlbi5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9kb20taGVscGVycy9lc20vdHJpZ2dlckV2ZW50LmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL2RvbS1oZWxwZXJzL2VzbS90cmFuc2l0aW9uRW5kLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LWJvb3RzdHJhcC9lc20vdHJhbnNpdGlvbkVuZExpc3RlbmVyLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LWJvb3RzdHJhcC9lc20vY3JlYXRlQ2hhaW5lZEZ1bmN0aW9uLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LWJvb3RzdHJhcC9lc20vdHJpZ2dlckJyb3dzZXJSZWZsb3cuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvQHJlc3RhcnQvaG9va3MvZXNtL3VzZU1lcmdlZFJlZnMuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS9zYWZlRmluZERPTU5vZGUuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS9UcmFuc2l0aW9uV3JhcHBlci5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9yZWFjdC1ib290c3RyYXAvZXNtL0NvbGxhcHNlLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LWJvb3RzdHJhcC9lc20vQWNjb3JkaW9uQ29udGV4dC5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9yZWFjdC1ib290c3RyYXAvZXNtL0FjY29yZGlvbkNvbGxhcHNlLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LWJvb3RzdHJhcC9lc20vQWNjb3JkaW9uSXRlbUNvbnRleHQuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS9BY2NvcmRpb25Cb2R5LmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LWJvb3RzdHJhcC9lc20vQWNjb3JkaW9uQnV0dG9uLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LWJvb3RzdHJhcC9lc20vQWNjb3JkaW9uSGVhZGVyLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LWJvb3RzdHJhcC9lc20vQWNjb3JkaW9uSXRlbS5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9yZWFjdC1ib290c3RyYXAvZXNtL0FjY29yZGlvbi5qcyIsIi4uLy4uLy4uLy4uLy4uL3NyYy9BY2NvcmRpYW4udHN4Il0sInNvdXJjZXNDb250ZW50IjpbIi8qIVxuXHRDb3B5cmlnaHQgKGMpIDIwMTggSmVkIFdhdHNvbi5cblx0TGljZW5zZWQgdW5kZXIgdGhlIE1JVCBMaWNlbnNlIChNSVQpLCBzZWVcblx0aHR0cDovL2plZHdhdHNvbi5naXRodWIuaW8vY2xhc3NuYW1lc1xuKi9cbi8qIGdsb2JhbCBkZWZpbmUgKi9cblxuKGZ1bmN0aW9uICgpIHtcblx0J3VzZSBzdHJpY3QnO1xuXG5cdHZhciBoYXNPd24gPSB7fS5oYXNPd25Qcm9wZXJ0eTtcblx0dmFyIG5hdGl2ZUNvZGVTdHJpbmcgPSAnW25hdGl2ZSBjb2RlXSc7XG5cblx0ZnVuY3Rpb24gY2xhc3NOYW1lcygpIHtcblx0XHR2YXIgY2xhc3NlcyA9IFtdO1xuXG5cdFx0Zm9yICh2YXIgaSA9IDA7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcblx0XHRcdHZhciBhcmcgPSBhcmd1bWVudHNbaV07XG5cdFx0XHRpZiAoIWFyZykgY29udGludWU7XG5cblx0XHRcdHZhciBhcmdUeXBlID0gdHlwZW9mIGFyZztcblxuXHRcdFx0aWYgKGFyZ1R5cGUgPT09ICdzdHJpbmcnIHx8IGFyZ1R5cGUgPT09ICdudW1iZXInKSB7XG5cdFx0XHRcdGNsYXNzZXMucHVzaChhcmcpO1xuXHRcdFx0fSBlbHNlIGlmIChBcnJheS5pc0FycmF5KGFyZykpIHtcblx0XHRcdFx0aWYgKGFyZy5sZW5ndGgpIHtcblx0XHRcdFx0XHR2YXIgaW5uZXIgPSBjbGFzc05hbWVzLmFwcGx5KG51bGwsIGFyZyk7XG5cdFx0XHRcdFx0aWYgKGlubmVyKSB7XG5cdFx0XHRcdFx0XHRjbGFzc2VzLnB1c2goaW5uZXIpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fSBlbHNlIGlmIChhcmdUeXBlID09PSAnb2JqZWN0Jykge1xuXHRcdFx0XHRpZiAoYXJnLnRvU3RyaW5nICE9PSBPYmplY3QucHJvdG90eXBlLnRvU3RyaW5nICYmICFhcmcudG9TdHJpbmcudG9TdHJpbmcoKS5pbmNsdWRlcygnW25hdGl2ZSBjb2RlXScpKSB7XG5cdFx0XHRcdFx0Y2xhc3Nlcy5wdXNoKGFyZy50b1N0cmluZygpKTtcblx0XHRcdFx0XHRjb250aW51ZTtcblx0XHRcdFx0fVxuXG5cdFx0XHRcdGZvciAodmFyIGtleSBpbiBhcmcpIHtcblx0XHRcdFx0XHRpZiAoaGFzT3duLmNhbGwoYXJnLCBrZXkpICYmIGFyZ1trZXldKSB7XG5cdFx0XHRcdFx0XHRjbGFzc2VzLnB1c2goa2V5KTtcblx0XHRcdFx0XHR9XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cblx0XHRyZXR1cm4gY2xhc3Nlcy5qb2luKCcgJyk7XG5cdH1cblxuXHRpZiAodHlwZW9mIG1vZHVsZSAhPT0gJ3VuZGVmaW5lZCcgJiYgbW9kdWxlLmV4cG9ydHMpIHtcblx0XHRjbGFzc05hbWVzLmRlZmF1bHQgPSBjbGFzc05hbWVzO1xuXHRcdG1vZHVsZS5leHBvcnRzID0gY2xhc3NOYW1lcztcblx0fSBlbHNlIGlmICh0eXBlb2YgZGVmaW5lID09PSAnZnVuY3Rpb24nICYmIHR5cGVvZiBkZWZpbmUuYW1kID09PSAnb2JqZWN0JyAmJiBkZWZpbmUuYW1kKSB7XG5cdFx0Ly8gcmVnaXN0ZXIgYXMgJ2NsYXNzbmFtZXMnLCBjb25zaXN0ZW50IHdpdGggbnBtIHBhY2thZ2UgbmFtZVxuXHRcdGRlZmluZSgnY2xhc3NuYW1lcycsIFtdLCBmdW5jdGlvbiAoKSB7XG5cdFx0XHRyZXR1cm4gY2xhc3NOYW1lcztcblx0XHR9KTtcblx0fSBlbHNlIHtcblx0XHR3aW5kb3cuY2xhc3NOYW1lcyA9IGNsYXNzTmFtZXM7XG5cdH1cbn0oKSk7XG4iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBfZXh0ZW5kcygpIHtcbiAgX2V4dGVuZHMgPSBPYmplY3QuYXNzaWduID8gT2JqZWN0LmFzc2lnbi5iaW5kKCkgOiBmdW5jdGlvbiAodGFyZ2V0KSB7XG4gICAgZm9yICh2YXIgaSA9IDE7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIHtcbiAgICAgIHZhciBzb3VyY2UgPSBhcmd1bWVudHNbaV07XG4gICAgICBmb3IgKHZhciBrZXkgaW4gc291cmNlKSB7XG4gICAgICAgIGlmIChPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwoc291cmNlLCBrZXkpKSB7XG4gICAgICAgICAgdGFyZ2V0W2tleV0gPSBzb3VyY2Vba2V5XTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gdGFyZ2V0O1xuICB9O1xuICByZXR1cm4gX2V4dGVuZHMuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbn0iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBfb2JqZWN0V2l0aG91dFByb3BlcnRpZXNMb29zZShzb3VyY2UsIGV4Y2x1ZGVkKSB7XG4gIGlmIChzb3VyY2UgPT0gbnVsbCkgcmV0dXJuIHt9O1xuICB2YXIgdGFyZ2V0ID0ge307XG4gIHZhciBzb3VyY2VLZXlzID0gT2JqZWN0LmtleXMoc291cmNlKTtcbiAgdmFyIGtleSwgaTtcbiAgZm9yIChpID0gMDsgaSA8IHNvdXJjZUtleXMubGVuZ3RoOyBpKyspIHtcbiAgICBrZXkgPSBzb3VyY2VLZXlzW2ldO1xuICAgIGlmIChleGNsdWRlZC5pbmRleE9mKGtleSkgPj0gMCkgY29udGludWU7XG4gICAgdGFyZ2V0W2tleV0gPSBzb3VyY2Vba2V5XTtcbiAgfVxuICByZXR1cm4gdGFyZ2V0O1xufSIsImltcG9ydCBpbnZhcmlhbnQgZnJvbSAnaW52YXJpYW50JztcblxudmFyIG5vb3AgPSBmdW5jdGlvbiBub29wKCkge307XG5cbmZ1bmN0aW9uIHJlYWRPbmx5UHJvcFR5cGUoaGFuZGxlciwgbmFtZSkge1xuICByZXR1cm4gZnVuY3Rpb24gKHByb3BzLCBwcm9wTmFtZSkge1xuICAgIGlmIChwcm9wc1twcm9wTmFtZV0gIT09IHVuZGVmaW5lZCkge1xuICAgICAgaWYgKCFwcm9wc1toYW5kbGVyXSkge1xuICAgICAgICByZXR1cm4gbmV3IEVycm9yKFwiWW91IGhhdmUgcHJvdmlkZWQgYSBgXCIgKyBwcm9wTmFtZSArIFwiYCBwcm9wIHRvIGBcIiArIG5hbWUgKyBcImAgXCIgKyAoXCJ3aXRob3V0IGFuIGBcIiArIGhhbmRsZXIgKyBcImAgaGFuZGxlciBwcm9wLiBUaGlzIHdpbGwgcmVuZGVyIGEgcmVhZC1vbmx5IGZpZWxkLiBcIikgKyAoXCJJZiB0aGUgZmllbGQgc2hvdWxkIGJlIG11dGFibGUgdXNlIGBcIiArIGRlZmF1bHRLZXkocHJvcE5hbWUpICsgXCJgLiBcIikgKyAoXCJPdGhlcndpc2UsIHNldCBgXCIgKyBoYW5kbGVyICsgXCJgLlwiKSk7XG4gICAgICB9XG4gICAgfVxuICB9O1xufVxuXG5leHBvcnQgZnVuY3Rpb24gdW5jb250cm9sbGVkUHJvcFR5cGVzKGNvbnRyb2xsZWRWYWx1ZXMsIGRpc3BsYXlOYW1lKSB7XG4gIHZhciBwcm9wVHlwZXMgPSB7fTtcbiAgT2JqZWN0LmtleXMoY29udHJvbGxlZFZhbHVlcykuZm9yRWFjaChmdW5jdGlvbiAocHJvcCkge1xuICAgIC8vIGFkZCBkZWZhdWx0IHByb3BUeXBlcyBmb3IgZm9sa3MgdGhhdCB1c2UgcnVudGltZSBjaGVja3NcbiAgICBwcm9wVHlwZXNbZGVmYXVsdEtleShwcm9wKV0gPSBub29wO1xuXG4gICAgaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicpIHtcbiAgICAgIHZhciBoYW5kbGVyID0gY29udHJvbGxlZFZhbHVlc1twcm9wXTtcbiAgICAgICEodHlwZW9mIGhhbmRsZXIgPT09ICdzdHJpbmcnICYmIGhhbmRsZXIudHJpbSgpLmxlbmd0aCkgPyBwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gXCJwcm9kdWN0aW9uXCIgPyBpbnZhcmlhbnQoZmFsc2UsICdVbmNvbnRyb2xsYWJsZSAtIFslc106IHRoZSBwcm9wIGAlc2AgbmVlZHMgYSB2YWxpZCBoYW5kbGVyIGtleSBuYW1lIGluIG9yZGVyIHRvIG1ha2UgaXQgdW5jb250cm9sbGFibGUnLCBkaXNwbGF5TmFtZSwgcHJvcCkgOiBpbnZhcmlhbnQoZmFsc2UpIDogdm9pZCAwO1xuICAgICAgcHJvcFR5cGVzW3Byb3BdID0gcmVhZE9ubHlQcm9wVHlwZShoYW5kbGVyLCBkaXNwbGF5TmFtZSk7XG4gICAgfVxuICB9KTtcbiAgcmV0dXJuIHByb3BUeXBlcztcbn1cbmV4cG9ydCBmdW5jdGlvbiBpc1Byb3AocHJvcHMsIHByb3ApIHtcbiAgcmV0dXJuIHByb3BzW3Byb3BdICE9PSB1bmRlZmluZWQ7XG59XG5leHBvcnQgZnVuY3Rpb24gZGVmYXVsdEtleShrZXkpIHtcbiAgcmV0dXJuICdkZWZhdWx0JyArIGtleS5jaGFyQXQoMCkudG9VcHBlckNhc2UoKSArIGtleS5zdWJzdHIoMSk7XG59XG4vKipcbiAqIENvcHlyaWdodCAoYykgMjAxMy1wcmVzZW50LCBGYWNlYm9vaywgSW5jLlxuICogQWxsIHJpZ2h0cyByZXNlcnZlZC5cbiAqXG4gKiBUaGlzIHNvdXJjZSBjb2RlIGlzIGxpY2Vuc2VkIHVuZGVyIHRoZSBCU0Qtc3R5bGUgbGljZW5zZSBmb3VuZCBpbiB0aGVcbiAqIExJQ0VOU0UgZmlsZSBpbiB0aGUgcm9vdCBkaXJlY3Rvcnkgb2YgdGhpcyBzb3VyY2UgdHJlZS4gQW4gYWRkaXRpb25hbCBncmFudFxuICogb2YgcGF0ZW50IHJpZ2h0cyBjYW4gYmUgZm91bmQgaW4gdGhlIFBBVEVOVFMgZmlsZSBpbiB0aGUgc2FtZSBkaXJlY3RvcnkuXG4gKi9cblxuZXhwb3J0IGZ1bmN0aW9uIGNhbkFjY2VwdFJlZihjb21wb25lbnQpIHtcbiAgcmV0dXJuICEhY29tcG9uZW50ICYmICh0eXBlb2YgY29tcG9uZW50ICE9PSAnZnVuY3Rpb24nIHx8IGNvbXBvbmVudC5wcm90b3R5cGUgJiYgY29tcG9uZW50LnByb3RvdHlwZS5pc1JlYWN0Q29tcG9uZW50KTtcbn0iLCJpbXBvcnQgX2V4dGVuZHMgZnJvbSBcIkBiYWJlbC9ydW50aW1lL2hlbHBlcnMvZXNtL2V4dGVuZHNcIjtcbmltcG9ydCBfb2JqZWN0V2l0aG91dFByb3BlcnRpZXNMb29zZSBmcm9tIFwiQGJhYmVsL3J1bnRpbWUvaGVscGVycy9lc20vb2JqZWN0V2l0aG91dFByb3BlcnRpZXNMb29zZVwiO1xuXG5mdW5jdGlvbiBfdG9Qcm9wZXJ0eUtleShhcmcpIHsgdmFyIGtleSA9IF90b1ByaW1pdGl2ZShhcmcsIFwic3RyaW5nXCIpOyByZXR1cm4gdHlwZW9mIGtleSA9PT0gXCJzeW1ib2xcIiA/IGtleSA6IFN0cmluZyhrZXkpOyB9XG5cbmZ1bmN0aW9uIF90b1ByaW1pdGl2ZShpbnB1dCwgaGludCkgeyBpZiAodHlwZW9mIGlucHV0ICE9PSBcIm9iamVjdFwiIHx8IGlucHV0ID09PSBudWxsKSByZXR1cm4gaW5wdXQ7IHZhciBwcmltID0gaW5wdXRbU3ltYm9sLnRvUHJpbWl0aXZlXTsgaWYgKHByaW0gIT09IHVuZGVmaW5lZCkgeyB2YXIgcmVzID0gcHJpbS5jYWxsKGlucHV0LCBoaW50IHx8IFwiZGVmYXVsdFwiKTsgaWYgKHR5cGVvZiByZXMgIT09IFwib2JqZWN0XCIpIHJldHVybiByZXM7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJAQHRvUHJpbWl0aXZlIG11c3QgcmV0dXJuIGEgcHJpbWl0aXZlIHZhbHVlLlwiKTsgfSByZXR1cm4gKGhpbnQgPT09IFwic3RyaW5nXCIgPyBTdHJpbmcgOiBOdW1iZXIpKGlucHV0KTsgfVxuXG5pbXBvcnQgeyB1c2VDYWxsYmFjaywgdXNlUmVmLCB1c2VTdGF0ZSB9IGZyb20gJ3JlYWN0JztcbmltcG9ydCAqIGFzIFV0aWxzIGZyb20gJy4vdXRpbHMnO1xuXG5mdW5jdGlvbiB1c2VVbmNvbnRyb2xsZWRQcm9wKHByb3BWYWx1ZSwgZGVmYXVsdFZhbHVlLCBoYW5kbGVyKSB7XG4gIHZhciB3YXNQcm9wUmVmID0gdXNlUmVmKHByb3BWYWx1ZSAhPT0gdW5kZWZpbmVkKTtcblxuICB2YXIgX3VzZVN0YXRlID0gdXNlU3RhdGUoZGVmYXVsdFZhbHVlKSxcbiAgICAgIHN0YXRlVmFsdWUgPSBfdXNlU3RhdGVbMF0sXG4gICAgICBzZXRTdGF0ZSA9IF91c2VTdGF0ZVsxXTtcblxuICB2YXIgaXNQcm9wID0gcHJvcFZhbHVlICE9PSB1bmRlZmluZWQ7XG4gIHZhciB3YXNQcm9wID0gd2FzUHJvcFJlZi5jdXJyZW50O1xuICB3YXNQcm9wUmVmLmN1cnJlbnQgPSBpc1Byb3A7XG4gIC8qKlxuICAgKiBJZiBhIHByb3Agc3dpdGNoZXMgZnJvbSBjb250cm9sbGVkIHRvIFVuY29udHJvbGxlZFxuICAgKiByZXNldCBpdHMgdmFsdWUgdG8gdGhlIGRlZmF1bHRWYWx1ZVxuICAgKi9cblxuICBpZiAoIWlzUHJvcCAmJiB3YXNQcm9wICYmIHN0YXRlVmFsdWUgIT09IGRlZmF1bHRWYWx1ZSkge1xuICAgIHNldFN0YXRlKGRlZmF1bHRWYWx1ZSk7XG4gIH1cblxuICByZXR1cm4gW2lzUHJvcCA/IHByb3BWYWx1ZSA6IHN0YXRlVmFsdWUsIHVzZUNhbGxiYWNrKGZ1bmN0aW9uICh2YWx1ZSkge1xuICAgIGZvciAodmFyIF9sZW4gPSBhcmd1bWVudHMubGVuZ3RoLCBhcmdzID0gbmV3IEFycmF5KF9sZW4gPiAxID8gX2xlbiAtIDEgOiAwKSwgX2tleSA9IDE7IF9rZXkgPCBfbGVuOyBfa2V5KyspIHtcbiAgICAgIGFyZ3NbX2tleSAtIDFdID0gYXJndW1lbnRzW19rZXldO1xuICAgIH1cblxuICAgIGlmIChoYW5kbGVyKSBoYW5kbGVyLmFwcGx5KHZvaWQgMCwgW3ZhbHVlXS5jb25jYXQoYXJncykpO1xuICAgIHNldFN0YXRlKHZhbHVlKTtcbiAgfSwgW2hhbmRsZXJdKV07XG59XG5cbmV4cG9ydCB7IHVzZVVuY29udHJvbGxlZFByb3AgfTtcbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIHVzZVVuY29udHJvbGxlZChwcm9wcywgY29uZmlnKSB7XG4gIHJldHVybiBPYmplY3Qua2V5cyhjb25maWcpLnJlZHVjZShmdW5jdGlvbiAocmVzdWx0LCBmaWVsZE5hbWUpIHtcbiAgICB2YXIgX2V4dGVuZHMyO1xuXG4gICAgdmFyIF9yZWYgPSByZXN1bHQsXG4gICAgICAgIGRlZmF1bHRWYWx1ZSA9IF9yZWZbVXRpbHMuZGVmYXVsdEtleShmaWVsZE5hbWUpXSxcbiAgICAgICAgcHJvcHNWYWx1ZSA9IF9yZWZbZmllbGROYW1lXSxcbiAgICAgICAgcmVzdCA9IF9vYmplY3RXaXRob3V0UHJvcGVydGllc0xvb3NlKF9yZWYsIFtVdGlscy5kZWZhdWx0S2V5KGZpZWxkTmFtZSksIGZpZWxkTmFtZV0ubWFwKF90b1Byb3BlcnR5S2V5KSk7XG5cbiAgICB2YXIgaGFuZGxlck5hbWUgPSBjb25maWdbZmllbGROYW1lXTtcblxuICAgIHZhciBfdXNlVW5jb250cm9sbGVkUHJvcCA9IHVzZVVuY29udHJvbGxlZFByb3AocHJvcHNWYWx1ZSwgZGVmYXVsdFZhbHVlLCBwcm9wc1toYW5kbGVyTmFtZV0pLFxuICAgICAgICB2YWx1ZSA9IF91c2VVbmNvbnRyb2xsZWRQcm9wWzBdLFxuICAgICAgICBoYW5kbGVyID0gX3VzZVVuY29udHJvbGxlZFByb3BbMV07XG5cbiAgICByZXR1cm4gX2V4dGVuZHMoe30sIHJlc3QsIChfZXh0ZW5kczIgPSB7fSwgX2V4dGVuZHMyW2ZpZWxkTmFtZV0gPSB2YWx1ZSwgX2V4dGVuZHMyW2hhbmRsZXJOYW1lXSA9IGhhbmRsZXIsIF9leHRlbmRzMikpO1xuICB9LCBwcm9wcyk7XG59IiwiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gX3NldFByb3RvdHlwZU9mKG8sIHApIHtcbiAgX3NldFByb3RvdHlwZU9mID0gT2JqZWN0LnNldFByb3RvdHlwZU9mID8gT2JqZWN0LnNldFByb3RvdHlwZU9mLmJpbmQoKSA6IGZ1bmN0aW9uIF9zZXRQcm90b3R5cGVPZihvLCBwKSB7XG4gICAgby5fX3Byb3RvX18gPSBwO1xuICAgIHJldHVybiBvO1xuICB9O1xuICByZXR1cm4gX3NldFByb3RvdHlwZU9mKG8sIHApO1xufSIsImltcG9ydCBzZXRQcm90b3R5cGVPZiBmcm9tIFwiLi9zZXRQcm90b3R5cGVPZi5qc1wiO1xuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gX2luaGVyaXRzTG9vc2Uoc3ViQ2xhc3MsIHN1cGVyQ2xhc3MpIHtcbiAgc3ViQ2xhc3MucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShzdXBlckNsYXNzLnByb3RvdHlwZSk7XG4gIHN1YkNsYXNzLnByb3RvdHlwZS5jb25zdHJ1Y3RvciA9IHN1YkNsYXNzO1xuICBzZXRQcm90b3R5cGVPZihzdWJDbGFzcywgc3VwZXJDbGFzcyk7XG59IiwiaW1wb3J0ICogYXMgUmVhY3QgZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsgdXNlQ29udGV4dCwgdXNlTWVtbyB9IGZyb20gJ3JlYWN0JztcbmltcG9ydCB7IGpzeCBhcyBfanN4IH0gZnJvbSBcInJlYWN0L2pzeC1ydW50aW1lXCI7XG5leHBvcnQgY29uc3QgREVGQVVMVF9CUkVBS1BPSU5UUyA9IFsneHhsJywgJ3hsJywgJ2xnJywgJ21kJywgJ3NtJywgJ3hzJ107XG5leHBvcnQgY29uc3QgREVGQVVMVF9NSU5fQlJFQUtQT0lOVCA9ICd4cyc7XG5jb25zdCBUaGVtZUNvbnRleHQgPSAvKiNfX1BVUkVfXyovUmVhY3QuY3JlYXRlQ29udGV4dCh7XG4gIHByZWZpeGVzOiB7fSxcbiAgYnJlYWtwb2ludHM6IERFRkFVTFRfQlJFQUtQT0lOVFMsXG4gIG1pbkJyZWFrcG9pbnQ6IERFRkFVTFRfTUlOX0JSRUFLUE9JTlRcbn0pO1xuY29uc3Qge1xuICBDb25zdW1lcixcbiAgUHJvdmlkZXJcbn0gPSBUaGVtZUNvbnRleHQ7XG5mdW5jdGlvbiBUaGVtZVByb3ZpZGVyKHtcbiAgcHJlZml4ZXMgPSB7fSxcbiAgYnJlYWtwb2ludHMgPSBERUZBVUxUX0JSRUFLUE9JTlRTLFxuICBtaW5CcmVha3BvaW50ID0gREVGQVVMVF9NSU5fQlJFQUtQT0lOVCxcbiAgZGlyLFxuICBjaGlsZHJlblxufSkge1xuICBjb25zdCBjb250ZXh0VmFsdWUgPSB1c2VNZW1vKCgpID0+ICh7XG4gICAgcHJlZml4ZXM6IHtcbiAgICAgIC4uLnByZWZpeGVzXG4gICAgfSxcbiAgICBicmVha3BvaW50cyxcbiAgICBtaW5CcmVha3BvaW50LFxuICAgIGRpclxuICB9KSwgW3ByZWZpeGVzLCBicmVha3BvaW50cywgbWluQnJlYWtwb2ludCwgZGlyXSk7XG4gIHJldHVybiAvKiNfX1BVUkVfXyovX2pzeChQcm92aWRlciwge1xuICAgIHZhbHVlOiBjb250ZXh0VmFsdWUsXG4gICAgY2hpbGRyZW46IGNoaWxkcmVuXG4gIH0pO1xufVxuZXhwb3J0IGZ1bmN0aW9uIHVzZUJvb3RzdHJhcFByZWZpeChwcmVmaXgsIGRlZmF1bHRQcmVmaXgpIHtcbiAgY29uc3Qge1xuICAgIHByZWZpeGVzXG4gIH0gPSB1c2VDb250ZXh0KFRoZW1lQ29udGV4dCk7XG4gIHJldHVybiBwcmVmaXggfHwgcHJlZml4ZXNbZGVmYXVsdFByZWZpeF0gfHwgZGVmYXVsdFByZWZpeDtcbn1cbmV4cG9ydCBmdW5jdGlvbiB1c2VCb290c3RyYXBCcmVha3BvaW50cygpIHtcbiAgY29uc3Qge1xuICAgIGJyZWFrcG9pbnRzXG4gIH0gPSB1c2VDb250ZXh0KFRoZW1lQ29udGV4dCk7XG4gIHJldHVybiBicmVha3BvaW50cztcbn1cbmV4cG9ydCBmdW5jdGlvbiB1c2VCb290c3RyYXBNaW5CcmVha3BvaW50KCkge1xuICBjb25zdCB7XG4gICAgbWluQnJlYWtwb2ludFxuICB9ID0gdXNlQ29udGV4dChUaGVtZUNvbnRleHQpO1xuICByZXR1cm4gbWluQnJlYWtwb2ludDtcbn1cbmV4cG9ydCBmdW5jdGlvbiB1c2VJc1JUTCgpIHtcbiAgY29uc3Qge1xuICAgIGRpclxuICB9ID0gdXNlQ29udGV4dChUaGVtZUNvbnRleHQpO1xuICByZXR1cm4gZGlyID09PSAncnRsJztcbn1cbmZ1bmN0aW9uIGNyZWF0ZUJvb3RzdHJhcENvbXBvbmVudChDb21wb25lbnQsIG9wdHMpIHtcbiAgaWYgKHR5cGVvZiBvcHRzID09PSAnc3RyaW5nJykgb3B0cyA9IHtcbiAgICBwcmVmaXg6IG9wdHNcbiAgfTtcbiAgY29uc3QgaXNDbGFzc3kgPSBDb21wb25lbnQucHJvdG90eXBlICYmIENvbXBvbmVudC5wcm90b3R5cGUuaXNSZWFjdENvbXBvbmVudDtcbiAgLy8gSWYgaXQncyBhIGZ1bmN0aW9uYWwgY29tcG9uZW50IG1ha2Ugc3VyZSB3ZSBkb24ndCBicmVhayBpdCB3aXRoIGEgcmVmXG4gIGNvbnN0IHtcbiAgICBwcmVmaXgsXG4gICAgZm9yd2FyZFJlZkFzID0gaXNDbGFzc3kgPyAncmVmJyA6ICdpbm5lclJlZidcbiAgfSA9IG9wdHM7XG4gIGNvbnN0IFdyYXBwZWQgPSAvKiNfX1BVUkVfXyovUmVhY3QuZm9yd2FyZFJlZigoe1xuICAgIC4uLnByb3BzXG4gIH0sIHJlZikgPT4ge1xuICAgIHByb3BzW2ZvcndhcmRSZWZBc10gPSByZWY7XG4gICAgY29uc3QgYnNQcmVmaXggPSB1c2VCb290c3RyYXBQcmVmaXgocHJvcHMuYnNQcmVmaXgsIHByZWZpeCk7XG4gICAgcmV0dXJuIC8qI19fUFVSRV9fKi9fanN4KENvbXBvbmVudCwge1xuICAgICAgLi4ucHJvcHMsXG4gICAgICBic1ByZWZpeDogYnNQcmVmaXhcbiAgICB9KTtcbiAgfSk7XG4gIFdyYXBwZWQuZGlzcGxheU5hbWUgPSBgQm9vdHN0cmFwKCR7Q29tcG9uZW50LmRpc3BsYXlOYW1lIHx8IENvbXBvbmVudC5uYW1lfSlgO1xuICByZXR1cm4gV3JhcHBlZDtcbn1cbmV4cG9ydCB7IGNyZWF0ZUJvb3RzdHJhcENvbXBvbmVudCwgQ29uc3VtZXIgYXMgVGhlbWVDb25zdW1lciB9O1xuZXhwb3J0IGRlZmF1bHQgVGhlbWVQcm92aWRlcjsiLCIvKipcbiAqIFJldHVybnMgdGhlIG93bmVyIGRvY3VtZW50IG9mIGEgZ2l2ZW4gZWxlbWVudC5cbiAqIFxuICogQHBhcmFtIG5vZGUgdGhlIGVsZW1lbnRcbiAqL1xuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gb3duZXJEb2N1bWVudChub2RlKSB7XG4gIHJldHVybiBub2RlICYmIG5vZGUub3duZXJEb2N1bWVudCB8fCBkb2N1bWVudDtcbn0iLCJpbXBvcnQgb3duZXJEb2N1bWVudCBmcm9tICcuL293bmVyRG9jdW1lbnQnO1xuLyoqXG4gKiBSZXR1cm5zIHRoZSBvd25lciB3aW5kb3cgb2YgYSBnaXZlbiBlbGVtZW50LlxuICogXG4gKiBAcGFyYW0gbm9kZSB0aGUgZWxlbWVudFxuICovXG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIG93bmVyV2luZG93KG5vZGUpIHtcbiAgdmFyIGRvYyA9IG93bmVyRG9jdW1lbnQobm9kZSk7XG4gIHJldHVybiBkb2MgJiYgZG9jLmRlZmF1bHRWaWV3IHx8IHdpbmRvdztcbn0iLCJpbXBvcnQgb3duZXJXaW5kb3cgZnJvbSAnLi9vd25lcldpbmRvdyc7XG4vKipcbiAqIFJldHVybnMgb25lIG9yIGFsbCBjb21wdXRlZCBzdHlsZSBwcm9wZXJ0aWVzIG9mIGFuIGVsZW1lbnQuXG4gKiBcbiAqIEBwYXJhbSBub2RlIHRoZSBlbGVtZW50XG4gKiBAcGFyYW0gcHN1ZWRvRWxlbWVudCB0aGUgc3R5bGUgcHJvcGVydHlcbiAqL1xuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBnZXRDb21wdXRlZFN0eWxlKG5vZGUsIHBzdWVkb0VsZW1lbnQpIHtcbiAgcmV0dXJuIG93bmVyV2luZG93KG5vZGUpLmdldENvbXB1dGVkU3R5bGUobm9kZSwgcHN1ZWRvRWxlbWVudCk7XG59IiwidmFyIHJVcHBlciA9IC8oW0EtWl0pL2c7XG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBoeXBoZW5hdGUoc3RyaW5nKSB7XG4gIHJldHVybiBzdHJpbmcucmVwbGFjZShyVXBwZXIsICctJDEnKS50b0xvd2VyQ2FzZSgpO1xufSIsIi8qKlxuICogQ29weXJpZ2h0IDIwMTMtMjAxNCwgRmFjZWJvb2ssIEluYy5cbiAqIEFsbCByaWdodHMgcmVzZXJ2ZWQuXG4gKiBodHRwczovL2dpdGh1Yi5jb20vZmFjZWJvb2svcmVhY3QvYmxvYi8yYWViOGEyYTZiZWIwMDYxN2E0MjE3ZjdmODI4NDkyNGZhMmFkODE5L3NyYy92ZW5kb3IvY29yZS9oeXBoZW5hdGVTdHlsZU5hbWUuanNcbiAqL1xuaW1wb3J0IGh5cGhlbmF0ZSBmcm9tICcuL2h5cGhlbmF0ZSc7XG52YXIgbXNQYXR0ZXJuID0gL15tcy0vO1xuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gaHlwaGVuYXRlU3R5bGVOYW1lKHN0cmluZykge1xuICByZXR1cm4gaHlwaGVuYXRlKHN0cmluZykucmVwbGFjZShtc1BhdHRlcm4sICctbXMtJyk7XG59IiwidmFyIHN1cHBvcnRlZFRyYW5zZm9ybXMgPSAvXigodHJhbnNsYXRlfHJvdGF0ZXxzY2FsZSkoWHxZfFp8M2QpP3xtYXRyaXgoM2QpP3xwZXJzcGVjdGl2ZXxza2V3KFh8WSk/KSQvaTtcbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIGlzVHJhbnNmb3JtKHZhbHVlKSB7XG4gIHJldHVybiAhISh2YWx1ZSAmJiBzdXBwb3J0ZWRUcmFuc2Zvcm1zLnRlc3QodmFsdWUpKTtcbn0iLCJpbXBvcnQgZ2V0Q29tcHV0ZWRTdHlsZSBmcm9tICcuL2dldENvbXB1dGVkU3R5bGUnO1xuaW1wb3J0IGh5cGhlbmF0ZSBmcm9tICcuL2h5cGhlbmF0ZVN0eWxlJztcbmltcG9ydCBpc1RyYW5zZm9ybSBmcm9tICcuL2lzVHJhbnNmb3JtJztcblxuZnVuY3Rpb24gc3R5bGUobm9kZSwgcHJvcGVydHkpIHtcbiAgdmFyIGNzcyA9ICcnO1xuICB2YXIgdHJhbnNmb3JtcyA9ICcnO1xuXG4gIGlmICh0eXBlb2YgcHJvcGVydHkgPT09ICdzdHJpbmcnKSB7XG4gICAgcmV0dXJuIG5vZGUuc3R5bGUuZ2V0UHJvcGVydHlWYWx1ZShoeXBoZW5hdGUocHJvcGVydHkpKSB8fCBnZXRDb21wdXRlZFN0eWxlKG5vZGUpLmdldFByb3BlcnR5VmFsdWUoaHlwaGVuYXRlKHByb3BlcnR5KSk7XG4gIH1cblxuICBPYmplY3Qua2V5cyhwcm9wZXJ0eSkuZm9yRWFjaChmdW5jdGlvbiAoa2V5KSB7XG4gICAgdmFyIHZhbHVlID0gcHJvcGVydHlba2V5XTtcblxuICAgIGlmICghdmFsdWUgJiYgdmFsdWUgIT09IDApIHtcbiAgICAgIG5vZGUuc3R5bGUucmVtb3ZlUHJvcGVydHkoaHlwaGVuYXRlKGtleSkpO1xuICAgIH0gZWxzZSBpZiAoaXNUcmFuc2Zvcm0oa2V5KSkge1xuICAgICAgdHJhbnNmb3JtcyArPSBrZXkgKyBcIihcIiArIHZhbHVlICsgXCIpIFwiO1xuICAgIH0gZWxzZSB7XG4gICAgICBjc3MgKz0gaHlwaGVuYXRlKGtleSkgKyBcIjogXCIgKyB2YWx1ZSArIFwiO1wiO1xuICAgIH1cbiAgfSk7XG5cbiAgaWYgKHRyYW5zZm9ybXMpIHtcbiAgICBjc3MgKz0gXCJ0cmFuc2Zvcm06IFwiICsgdHJhbnNmb3JtcyArIFwiO1wiO1xuICB9XG5cbiAgbm9kZS5zdHlsZS5jc3NUZXh0ICs9IFwiO1wiICsgY3NzO1xufVxuXG5leHBvcnQgZGVmYXVsdCBzdHlsZTsiLCIvKiogQGxpY2Vuc2UgUmVhY3QgdjE2LjEzLjFcbiAqIHJlYWN0LWlzLmRldmVsb3BtZW50LmpzXG4gKlxuICogQ29weXJpZ2h0IChjKSBGYWNlYm9vaywgSW5jLiBhbmQgaXRzIGFmZmlsaWF0ZXMuXG4gKlxuICogVGhpcyBzb3VyY2UgY29kZSBpcyBsaWNlbnNlZCB1bmRlciB0aGUgTUlUIGxpY2Vuc2UgZm91bmQgaW4gdGhlXG4gKiBMSUNFTlNFIGZpbGUgaW4gdGhlIHJvb3QgZGlyZWN0b3J5IG9mIHRoaXMgc291cmNlIHRyZWUuXG4gKi9cblxuJ3VzZSBzdHJpY3QnO1xuXG5cblxuaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSBcInByb2R1Y3Rpb25cIikge1xuICAoZnVuY3Rpb24oKSB7XG4ndXNlIHN0cmljdCc7XG5cbi8vIFRoZSBTeW1ib2wgdXNlZCB0byB0YWcgdGhlIFJlYWN0RWxlbWVudC1saWtlIHR5cGVzLiBJZiB0aGVyZSBpcyBubyBuYXRpdmUgU3ltYm9sXG4vLyBub3IgcG9seWZpbGwsIHRoZW4gYSBwbGFpbiBudW1iZXIgaXMgdXNlZCBmb3IgcGVyZm9ybWFuY2UuXG52YXIgaGFzU3ltYm9sID0gdHlwZW9mIFN5bWJvbCA9PT0gJ2Z1bmN0aW9uJyAmJiBTeW1ib2wuZm9yO1xudmFyIFJFQUNUX0VMRU1FTlRfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmVsZW1lbnQnKSA6IDB4ZWFjNztcbnZhciBSRUFDVF9QT1JUQUxfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LnBvcnRhbCcpIDogMHhlYWNhO1xudmFyIFJFQUNUX0ZSQUdNRU5UX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5mcmFnbWVudCcpIDogMHhlYWNiO1xudmFyIFJFQUNUX1NUUklDVF9NT0RFX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5zdHJpY3RfbW9kZScpIDogMHhlYWNjO1xudmFyIFJFQUNUX1BST0ZJTEVSX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5wcm9maWxlcicpIDogMHhlYWQyO1xudmFyIFJFQUNUX1BST1ZJREVSX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5wcm92aWRlcicpIDogMHhlYWNkO1xudmFyIFJFQUNUX0NPTlRFWFRfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmNvbnRleHQnKSA6IDB4ZWFjZTsgLy8gVE9ETzogV2UgZG9uJ3QgdXNlIEFzeW5jTW9kZSBvciBDb25jdXJyZW50TW9kZSBhbnltb3JlLiBUaGV5IHdlcmUgdGVtcG9yYXJ5XG4vLyAodW5zdGFibGUpIEFQSXMgdGhhdCBoYXZlIGJlZW4gcmVtb3ZlZC4gQ2FuIHdlIHJlbW92ZSB0aGUgc3ltYm9scz9cblxudmFyIFJFQUNUX0FTWU5DX01PREVfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmFzeW5jX21vZGUnKSA6IDB4ZWFjZjtcbnZhciBSRUFDVF9DT05DVVJSRU5UX01PREVfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmNvbmN1cnJlbnRfbW9kZScpIDogMHhlYWNmO1xudmFyIFJFQUNUX0ZPUldBUkRfUkVGX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5mb3J3YXJkX3JlZicpIDogMHhlYWQwO1xudmFyIFJFQUNUX1NVU1BFTlNFX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5zdXNwZW5zZScpIDogMHhlYWQxO1xudmFyIFJFQUNUX1NVU1BFTlNFX0xJU1RfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LnN1c3BlbnNlX2xpc3QnKSA6IDB4ZWFkODtcbnZhciBSRUFDVF9NRU1PX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5tZW1vJykgOiAweGVhZDM7XG52YXIgUkVBQ1RfTEFaWV9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QubGF6eScpIDogMHhlYWQ0O1xudmFyIFJFQUNUX0JMT0NLX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5ibG9jaycpIDogMHhlYWQ5O1xudmFyIFJFQUNUX0ZVTkRBTUVOVEFMX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5mdW5kYW1lbnRhbCcpIDogMHhlYWQ1O1xudmFyIFJFQUNUX1JFU1BPTkRFUl9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QucmVzcG9uZGVyJykgOiAweGVhZDY7XG52YXIgUkVBQ1RfU0NPUEVfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LnNjb3BlJykgOiAweGVhZDc7XG5cbmZ1bmN0aW9uIGlzVmFsaWRFbGVtZW50VHlwZSh0eXBlKSB7XG4gIHJldHVybiB0eXBlb2YgdHlwZSA9PT0gJ3N0cmluZycgfHwgdHlwZW9mIHR5cGUgPT09ICdmdW5jdGlvbicgfHwgLy8gTm90ZTogaXRzIHR5cGVvZiBtaWdodCBiZSBvdGhlciB0aGFuICdzeW1ib2wnIG9yICdudW1iZXInIGlmIGl0J3MgYSBwb2x5ZmlsbC5cbiAgdHlwZSA9PT0gUkVBQ1RfRlJBR01FTlRfVFlQRSB8fCB0eXBlID09PSBSRUFDVF9DT05DVVJSRU5UX01PREVfVFlQRSB8fCB0eXBlID09PSBSRUFDVF9QUk9GSUxFUl9UWVBFIHx8IHR5cGUgPT09IFJFQUNUX1NUUklDVF9NT0RFX1RZUEUgfHwgdHlwZSA9PT0gUkVBQ1RfU1VTUEVOU0VfVFlQRSB8fCB0eXBlID09PSBSRUFDVF9TVVNQRU5TRV9MSVNUX1RZUEUgfHwgdHlwZW9mIHR5cGUgPT09ICdvYmplY3QnICYmIHR5cGUgIT09IG51bGwgJiYgKHR5cGUuJCR0eXBlb2YgPT09IFJFQUNUX0xBWllfVFlQRSB8fCB0eXBlLiQkdHlwZW9mID09PSBSRUFDVF9NRU1PX1RZUEUgfHwgdHlwZS4kJHR5cGVvZiA9PT0gUkVBQ1RfUFJPVklERVJfVFlQRSB8fCB0eXBlLiQkdHlwZW9mID09PSBSRUFDVF9DT05URVhUX1RZUEUgfHwgdHlwZS4kJHR5cGVvZiA9PT0gUkVBQ1RfRk9SV0FSRF9SRUZfVFlQRSB8fCB0eXBlLiQkdHlwZW9mID09PSBSRUFDVF9GVU5EQU1FTlRBTF9UWVBFIHx8IHR5cGUuJCR0eXBlb2YgPT09IFJFQUNUX1JFU1BPTkRFUl9UWVBFIHx8IHR5cGUuJCR0eXBlb2YgPT09IFJFQUNUX1NDT1BFX1RZUEUgfHwgdHlwZS4kJHR5cGVvZiA9PT0gUkVBQ1RfQkxPQ0tfVFlQRSk7XG59XG5cbmZ1bmN0aW9uIHR5cGVPZihvYmplY3QpIHtcbiAgaWYgKHR5cGVvZiBvYmplY3QgPT09ICdvYmplY3QnICYmIG9iamVjdCAhPT0gbnVsbCkge1xuICAgIHZhciAkJHR5cGVvZiA9IG9iamVjdC4kJHR5cGVvZjtcblxuICAgIHN3aXRjaCAoJCR0eXBlb2YpIHtcbiAgICAgIGNhc2UgUkVBQ1RfRUxFTUVOVF9UWVBFOlxuICAgICAgICB2YXIgdHlwZSA9IG9iamVjdC50eXBlO1xuXG4gICAgICAgIHN3aXRjaCAodHlwZSkge1xuICAgICAgICAgIGNhc2UgUkVBQ1RfQVNZTkNfTU9ERV9UWVBFOlxuICAgICAgICAgIGNhc2UgUkVBQ1RfQ09OQ1VSUkVOVF9NT0RFX1RZUEU6XG4gICAgICAgICAgY2FzZSBSRUFDVF9GUkFHTUVOVF9UWVBFOlxuICAgICAgICAgIGNhc2UgUkVBQ1RfUFJPRklMRVJfVFlQRTpcbiAgICAgICAgICBjYXNlIFJFQUNUX1NUUklDVF9NT0RFX1RZUEU6XG4gICAgICAgICAgY2FzZSBSRUFDVF9TVVNQRU5TRV9UWVBFOlxuICAgICAgICAgICAgcmV0dXJuIHR5cGU7XG5cbiAgICAgICAgICBkZWZhdWx0OlxuICAgICAgICAgICAgdmFyICQkdHlwZW9mVHlwZSA9IHR5cGUgJiYgdHlwZS4kJHR5cGVvZjtcblxuICAgICAgICAgICAgc3dpdGNoICgkJHR5cGVvZlR5cGUpIHtcbiAgICAgICAgICAgICAgY2FzZSBSRUFDVF9DT05URVhUX1RZUEU6XG4gICAgICAgICAgICAgIGNhc2UgUkVBQ1RfRk9SV0FSRF9SRUZfVFlQRTpcbiAgICAgICAgICAgICAgY2FzZSBSRUFDVF9MQVpZX1RZUEU6XG4gICAgICAgICAgICAgIGNhc2UgUkVBQ1RfTUVNT19UWVBFOlxuICAgICAgICAgICAgICBjYXNlIFJFQUNUX1BST1ZJREVSX1RZUEU6XG4gICAgICAgICAgICAgICAgcmV0dXJuICQkdHlwZW9mVHlwZTtcblxuICAgICAgICAgICAgICBkZWZhdWx0OlxuICAgICAgICAgICAgICAgIHJldHVybiAkJHR5cGVvZjtcbiAgICAgICAgICAgIH1cblxuICAgICAgICB9XG5cbiAgICAgIGNhc2UgUkVBQ1RfUE9SVEFMX1RZUEU6XG4gICAgICAgIHJldHVybiAkJHR5cGVvZjtcbiAgICB9XG4gIH1cblxuICByZXR1cm4gdW5kZWZpbmVkO1xufSAvLyBBc3luY01vZGUgaXMgZGVwcmVjYXRlZCBhbG9uZyB3aXRoIGlzQXN5bmNNb2RlXG5cbnZhciBBc3luY01vZGUgPSBSRUFDVF9BU1lOQ19NT0RFX1RZUEU7XG52YXIgQ29uY3VycmVudE1vZGUgPSBSRUFDVF9DT05DVVJSRU5UX01PREVfVFlQRTtcbnZhciBDb250ZXh0Q29uc3VtZXIgPSBSRUFDVF9DT05URVhUX1RZUEU7XG52YXIgQ29udGV4dFByb3ZpZGVyID0gUkVBQ1RfUFJPVklERVJfVFlQRTtcbnZhciBFbGVtZW50ID0gUkVBQ1RfRUxFTUVOVF9UWVBFO1xudmFyIEZvcndhcmRSZWYgPSBSRUFDVF9GT1JXQVJEX1JFRl9UWVBFO1xudmFyIEZyYWdtZW50ID0gUkVBQ1RfRlJBR01FTlRfVFlQRTtcbnZhciBMYXp5ID0gUkVBQ1RfTEFaWV9UWVBFO1xudmFyIE1lbW8gPSBSRUFDVF9NRU1PX1RZUEU7XG52YXIgUG9ydGFsID0gUkVBQ1RfUE9SVEFMX1RZUEU7XG52YXIgUHJvZmlsZXIgPSBSRUFDVF9QUk9GSUxFUl9UWVBFO1xudmFyIFN0cmljdE1vZGUgPSBSRUFDVF9TVFJJQ1RfTU9ERV9UWVBFO1xudmFyIFN1c3BlbnNlID0gUkVBQ1RfU1VTUEVOU0VfVFlQRTtcbnZhciBoYXNXYXJuZWRBYm91dERlcHJlY2F0ZWRJc0FzeW5jTW9kZSA9IGZhbHNlOyAvLyBBc3luY01vZGUgc2hvdWxkIGJlIGRlcHJlY2F0ZWRcblxuZnVuY3Rpb24gaXNBc3luY01vZGUob2JqZWN0KSB7XG4gIHtcbiAgICBpZiAoIWhhc1dhcm5lZEFib3V0RGVwcmVjYXRlZElzQXN5bmNNb2RlKSB7XG4gICAgICBoYXNXYXJuZWRBYm91dERlcHJlY2F0ZWRJc0FzeW5jTW9kZSA9IHRydWU7IC8vIFVzaW5nIGNvbnNvbGVbJ3dhcm4nXSB0byBldmFkZSBCYWJlbCBhbmQgRVNMaW50XG5cbiAgICAgIGNvbnNvbGVbJ3dhcm4nXSgnVGhlIFJlYWN0SXMuaXNBc3luY01vZGUoKSBhbGlhcyBoYXMgYmVlbiBkZXByZWNhdGVkLCAnICsgJ2FuZCB3aWxsIGJlIHJlbW92ZWQgaW4gUmVhY3QgMTcrLiBVcGRhdGUgeW91ciBjb2RlIHRvIHVzZSAnICsgJ1JlYWN0SXMuaXNDb25jdXJyZW50TW9kZSgpIGluc3RlYWQuIEl0IGhhcyB0aGUgZXhhY3Qgc2FtZSBBUEkuJyk7XG4gICAgfVxuICB9XG5cbiAgcmV0dXJuIGlzQ29uY3VycmVudE1vZGUob2JqZWN0KSB8fCB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfQVNZTkNfTU9ERV9UWVBFO1xufVxuZnVuY3Rpb24gaXNDb25jdXJyZW50TW9kZShvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9DT05DVVJSRU5UX01PREVfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzQ29udGV4dENvbnN1bWVyKG9iamVjdCkge1xuICByZXR1cm4gdHlwZU9mKG9iamVjdCkgPT09IFJFQUNUX0NPTlRFWFRfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzQ29udGV4dFByb3ZpZGVyKG9iamVjdCkge1xuICByZXR1cm4gdHlwZU9mKG9iamVjdCkgPT09IFJFQUNUX1BST1ZJREVSX1RZUEU7XG59XG5mdW5jdGlvbiBpc0VsZW1lbnQob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlb2Ygb2JqZWN0ID09PSAnb2JqZWN0JyAmJiBvYmplY3QgIT09IG51bGwgJiYgb2JqZWN0LiQkdHlwZW9mID09PSBSRUFDVF9FTEVNRU5UX1RZUEU7XG59XG5mdW5jdGlvbiBpc0ZvcndhcmRSZWYob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfRk9SV0FSRF9SRUZfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzRnJhZ21lbnQob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfRlJBR01FTlRfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzTGF6eShvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9MQVpZX1RZUEU7XG59XG5mdW5jdGlvbiBpc01lbW8ob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfTUVNT19UWVBFO1xufVxuZnVuY3Rpb24gaXNQb3J0YWwob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfUE9SVEFMX1RZUEU7XG59XG5mdW5jdGlvbiBpc1Byb2ZpbGVyKG9iamVjdCkge1xuICByZXR1cm4gdHlwZU9mKG9iamVjdCkgPT09IFJFQUNUX1BST0ZJTEVSX1RZUEU7XG59XG5mdW5jdGlvbiBpc1N0cmljdE1vZGUob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfU1RSSUNUX01PREVfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzU3VzcGVuc2Uob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfU1VTUEVOU0VfVFlQRTtcbn1cblxuZXhwb3J0cy5Bc3luY01vZGUgPSBBc3luY01vZGU7XG5leHBvcnRzLkNvbmN1cnJlbnRNb2RlID0gQ29uY3VycmVudE1vZGU7XG5leHBvcnRzLkNvbnRleHRDb25zdW1lciA9IENvbnRleHRDb25zdW1lcjtcbmV4cG9ydHMuQ29udGV4dFByb3ZpZGVyID0gQ29udGV4dFByb3ZpZGVyO1xuZXhwb3J0cy5FbGVtZW50ID0gRWxlbWVudDtcbmV4cG9ydHMuRm9yd2FyZFJlZiA9IEZvcndhcmRSZWY7XG5leHBvcnRzLkZyYWdtZW50ID0gRnJhZ21lbnQ7XG5leHBvcnRzLkxhenkgPSBMYXp5O1xuZXhwb3J0cy5NZW1vID0gTWVtbztcbmV4cG9ydHMuUG9ydGFsID0gUG9ydGFsO1xuZXhwb3J0cy5Qcm9maWxlciA9IFByb2ZpbGVyO1xuZXhwb3J0cy5TdHJpY3RNb2RlID0gU3RyaWN0TW9kZTtcbmV4cG9ydHMuU3VzcGVuc2UgPSBTdXNwZW5zZTtcbmV4cG9ydHMuaXNBc3luY01vZGUgPSBpc0FzeW5jTW9kZTtcbmV4cG9ydHMuaXNDb25jdXJyZW50TW9kZSA9IGlzQ29uY3VycmVudE1vZGU7XG5leHBvcnRzLmlzQ29udGV4dENvbnN1bWVyID0gaXNDb250ZXh0Q29uc3VtZXI7XG5leHBvcnRzLmlzQ29udGV4dFByb3ZpZGVyID0gaXNDb250ZXh0UHJvdmlkZXI7XG5leHBvcnRzLmlzRWxlbWVudCA9IGlzRWxlbWVudDtcbmV4cG9ydHMuaXNGb3J3YXJkUmVmID0gaXNGb3J3YXJkUmVmO1xuZXhwb3J0cy5pc0ZyYWdtZW50ID0gaXNGcmFnbWVudDtcbmV4cG9ydHMuaXNMYXp5ID0gaXNMYXp5O1xuZXhwb3J0cy5pc01lbW8gPSBpc01lbW87XG5leHBvcnRzLmlzUG9ydGFsID0gaXNQb3J0YWw7XG5leHBvcnRzLmlzUHJvZmlsZXIgPSBpc1Byb2ZpbGVyO1xuZXhwb3J0cy5pc1N0cmljdE1vZGUgPSBpc1N0cmljdE1vZGU7XG5leHBvcnRzLmlzU3VzcGVuc2UgPSBpc1N1c3BlbnNlO1xuZXhwb3J0cy5pc1ZhbGlkRWxlbWVudFR5cGUgPSBpc1ZhbGlkRWxlbWVudFR5cGU7XG5leHBvcnRzLnR5cGVPZiA9IHR5cGVPZjtcbiAgfSkoKTtcbn1cbiIsIid1c2Ugc3RyaWN0JztcblxuaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WID09PSAncHJvZHVjdGlvbicpIHtcbiAgbW9kdWxlLmV4cG9ydHMgPSByZXF1aXJlKCcuL2Nqcy9yZWFjdC1pcy5wcm9kdWN0aW9uLm1pbi5qcycpO1xufSBlbHNlIHtcbiAgbW9kdWxlLmV4cG9ydHMgPSByZXF1aXJlKCcuL2Nqcy9yZWFjdC1pcy5kZXZlbG9wbWVudC5qcycpO1xufVxuIiwiLypcbm9iamVjdC1hc3NpZ25cbihjKSBTaW5kcmUgU29yaHVzXG5AbGljZW5zZSBNSVRcbiovXG5cbid1c2Ugc3RyaWN0Jztcbi8qIGVzbGludC1kaXNhYmxlIG5vLXVudXNlZC12YXJzICovXG52YXIgZ2V0T3duUHJvcGVydHlTeW1ib2xzID0gT2JqZWN0LmdldE93blByb3BlcnR5U3ltYm9scztcbnZhciBoYXNPd25Qcm9wZXJ0eSA9IE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHk7XG52YXIgcHJvcElzRW51bWVyYWJsZSA9IE9iamVjdC5wcm90b3R5cGUucHJvcGVydHlJc0VudW1lcmFibGU7XG5cbmZ1bmN0aW9uIHRvT2JqZWN0KHZhbCkge1xuXHRpZiAodmFsID09PSBudWxsIHx8IHZhbCA9PT0gdW5kZWZpbmVkKSB7XG5cdFx0dGhyb3cgbmV3IFR5cGVFcnJvcignT2JqZWN0LmFzc2lnbiBjYW5ub3QgYmUgY2FsbGVkIHdpdGggbnVsbCBvciB1bmRlZmluZWQnKTtcblx0fVxuXG5cdHJldHVybiBPYmplY3QodmFsKTtcbn1cblxuZnVuY3Rpb24gc2hvdWxkVXNlTmF0aXZlKCkge1xuXHR0cnkge1xuXHRcdGlmICghT2JqZWN0LmFzc2lnbikge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdC8vIERldGVjdCBidWdneSBwcm9wZXJ0eSBlbnVtZXJhdGlvbiBvcmRlciBpbiBvbGRlciBWOCB2ZXJzaW9ucy5cblxuXHRcdC8vIGh0dHBzOi8vYnVncy5jaHJvbWl1bS5vcmcvcC92OC9pc3N1ZXMvZGV0YWlsP2lkPTQxMThcblx0XHR2YXIgdGVzdDEgPSBuZXcgU3RyaW5nKCdhYmMnKTsgIC8vIGVzbGludC1kaXNhYmxlLWxpbmUgbm8tbmV3LXdyYXBwZXJzXG5cdFx0dGVzdDFbNV0gPSAnZGUnO1xuXHRcdGlmIChPYmplY3QuZ2V0T3duUHJvcGVydHlOYW1lcyh0ZXN0MSlbMF0gPT09ICc1Jykge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdC8vIGh0dHBzOi8vYnVncy5jaHJvbWl1bS5vcmcvcC92OC9pc3N1ZXMvZGV0YWlsP2lkPTMwNTZcblx0XHR2YXIgdGVzdDIgPSB7fTtcblx0XHRmb3IgKHZhciBpID0gMDsgaSA8IDEwOyBpKyspIHtcblx0XHRcdHRlc3QyWydfJyArIFN0cmluZy5mcm9tQ2hhckNvZGUoaSldID0gaTtcblx0XHR9XG5cdFx0dmFyIG9yZGVyMiA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eU5hbWVzKHRlc3QyKS5tYXAoZnVuY3Rpb24gKG4pIHtcblx0XHRcdHJldHVybiB0ZXN0MltuXTtcblx0XHR9KTtcblx0XHRpZiAob3JkZXIyLmpvaW4oJycpICE9PSAnMDEyMzQ1Njc4OScpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cblx0XHQvLyBodHRwczovL2J1Z3MuY2hyb21pdW0ub3JnL3AvdjgvaXNzdWVzL2RldGFpbD9pZD0zMDU2XG5cdFx0dmFyIHRlc3QzID0ge307XG5cdFx0J2FiY2RlZmdoaWprbG1ub3BxcnN0Jy5zcGxpdCgnJykuZm9yRWFjaChmdW5jdGlvbiAobGV0dGVyKSB7XG5cdFx0XHR0ZXN0M1tsZXR0ZXJdID0gbGV0dGVyO1xuXHRcdH0pO1xuXHRcdGlmIChPYmplY3Qua2V5cyhPYmplY3QuYXNzaWduKHt9LCB0ZXN0MykpLmpvaW4oJycpICE9PVxuXHRcdFx0XHQnYWJjZGVmZ2hpamtsbW5vcHFyc3QnKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0cmV0dXJuIHRydWU7XG5cdH0gY2F0Y2ggKGVycikge1xuXHRcdC8vIFdlIGRvbid0IGV4cGVjdCBhbnkgb2YgdGhlIGFib3ZlIHRvIHRocm93LCBidXQgYmV0dGVyIHRvIGJlIHNhZmUuXG5cdFx0cmV0dXJuIGZhbHNlO1xuXHR9XG59XG5cbm1vZHVsZS5leHBvcnRzID0gc2hvdWxkVXNlTmF0aXZlKCkgPyBPYmplY3QuYXNzaWduIDogZnVuY3Rpb24gKHRhcmdldCwgc291cmNlKSB7XG5cdHZhciBmcm9tO1xuXHR2YXIgdG8gPSB0b09iamVjdCh0YXJnZXQpO1xuXHR2YXIgc3ltYm9scztcblxuXHRmb3IgKHZhciBzID0gMTsgcyA8IGFyZ3VtZW50cy5sZW5ndGg7IHMrKykge1xuXHRcdGZyb20gPSBPYmplY3QoYXJndW1lbnRzW3NdKTtcblxuXHRcdGZvciAodmFyIGtleSBpbiBmcm9tKSB7XG5cdFx0XHRpZiAoaGFzT3duUHJvcGVydHkuY2FsbChmcm9tLCBrZXkpKSB7XG5cdFx0XHRcdHRvW2tleV0gPSBmcm9tW2tleV07XG5cdFx0XHR9XG5cdFx0fVxuXG5cdFx0aWYgKGdldE93blByb3BlcnR5U3ltYm9scykge1xuXHRcdFx0c3ltYm9scyA9IGdldE93blByb3BlcnR5U3ltYm9scyhmcm9tKTtcblx0XHRcdGZvciAodmFyIGkgPSAwOyBpIDwgc3ltYm9scy5sZW5ndGg7IGkrKykge1xuXHRcdFx0XHRpZiAocHJvcElzRW51bWVyYWJsZS5jYWxsKGZyb20sIHN5bWJvbHNbaV0pKSB7XG5cdFx0XHRcdFx0dG9bc3ltYm9sc1tpXV0gPSBmcm9tW3N5bWJvbHNbaV1dO1xuXHRcdFx0XHR9XG5cdFx0XHR9XG5cdFx0fVxuXHR9XG5cblx0cmV0dXJuIHRvO1xufTtcbiIsIi8qKlxuICogQ29weXJpZ2h0IChjKSAyMDEzLXByZXNlbnQsIEZhY2Vib29rLCBJbmMuXG4gKlxuICogVGhpcyBzb3VyY2UgY29kZSBpcyBsaWNlbnNlZCB1bmRlciB0aGUgTUlUIGxpY2Vuc2UgZm91bmQgaW4gdGhlXG4gKiBMSUNFTlNFIGZpbGUgaW4gdGhlIHJvb3QgZGlyZWN0b3J5IG9mIHRoaXMgc291cmNlIHRyZWUuXG4gKi9cblxuJ3VzZSBzdHJpY3QnO1xuXG52YXIgUmVhY3RQcm9wVHlwZXNTZWNyZXQgPSAnU0VDUkVUX0RPX05PVF9QQVNTX1RISVNfT1JfWU9VX1dJTExfQkVfRklSRUQnO1xuXG5tb2R1bGUuZXhwb3J0cyA9IFJlYWN0UHJvcFR5cGVzU2VjcmV0O1xuIiwibW9kdWxlLmV4cG9ydHMgPSBGdW5jdGlvbi5jYWxsLmJpbmQoT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eSk7XG4iLCIvKipcbiAqIENvcHlyaWdodCAoYykgMjAxMy1wcmVzZW50LCBGYWNlYm9vaywgSW5jLlxuICpcbiAqIFRoaXMgc291cmNlIGNvZGUgaXMgbGljZW5zZWQgdW5kZXIgdGhlIE1JVCBsaWNlbnNlIGZvdW5kIGluIHRoZVxuICogTElDRU5TRSBmaWxlIGluIHRoZSByb290IGRpcmVjdG9yeSBvZiB0aGlzIHNvdXJjZSB0cmVlLlxuICovXG5cbid1c2Ugc3RyaWN0JztcblxudmFyIHByaW50V2FybmluZyA9IGZ1bmN0aW9uKCkge307XG5cbmlmIChwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gJ3Byb2R1Y3Rpb24nKSB7XG4gIHZhciBSZWFjdFByb3BUeXBlc1NlY3JldCA9IHJlcXVpcmUoJy4vbGliL1JlYWN0UHJvcFR5cGVzU2VjcmV0Jyk7XG4gIHZhciBsb2dnZWRUeXBlRmFpbHVyZXMgPSB7fTtcbiAgdmFyIGhhcyA9IHJlcXVpcmUoJy4vbGliL2hhcycpO1xuXG4gIHByaW50V2FybmluZyA9IGZ1bmN0aW9uKHRleHQpIHtcbiAgICB2YXIgbWVzc2FnZSA9ICdXYXJuaW5nOiAnICsgdGV4dDtcbiAgICBpZiAodHlwZW9mIGNvbnNvbGUgIT09ICd1bmRlZmluZWQnKSB7XG4gICAgICBjb25zb2xlLmVycm9yKG1lc3NhZ2UpO1xuICAgIH1cbiAgICB0cnkge1xuICAgICAgLy8gLS0tIFdlbGNvbWUgdG8gZGVidWdnaW5nIFJlYWN0IC0tLVxuICAgICAgLy8gVGhpcyBlcnJvciB3YXMgdGhyb3duIGFzIGEgY29udmVuaWVuY2Ugc28gdGhhdCB5b3UgY2FuIHVzZSB0aGlzIHN0YWNrXG4gICAgICAvLyB0byBmaW5kIHRoZSBjYWxsc2l0ZSB0aGF0IGNhdXNlZCB0aGlzIHdhcm5pbmcgdG8gZmlyZS5cbiAgICAgIHRocm93IG5ldyBFcnJvcihtZXNzYWdlKTtcbiAgICB9IGNhdGNoICh4KSB7IC8qKi8gfVxuICB9O1xufVxuXG4vKipcbiAqIEFzc2VydCB0aGF0IHRoZSB2YWx1ZXMgbWF0Y2ggd2l0aCB0aGUgdHlwZSBzcGVjcy5cbiAqIEVycm9yIG1lc3NhZ2VzIGFyZSBtZW1vcml6ZWQgYW5kIHdpbGwgb25seSBiZSBzaG93biBvbmNlLlxuICpcbiAqIEBwYXJhbSB7b2JqZWN0fSB0eXBlU3BlY3MgTWFwIG9mIG5hbWUgdG8gYSBSZWFjdFByb3BUeXBlXG4gKiBAcGFyYW0ge29iamVjdH0gdmFsdWVzIFJ1bnRpbWUgdmFsdWVzIHRoYXQgbmVlZCB0byBiZSB0eXBlLWNoZWNrZWRcbiAqIEBwYXJhbSB7c3RyaW5nfSBsb2NhdGlvbiBlLmcuIFwicHJvcFwiLCBcImNvbnRleHRcIiwgXCJjaGlsZCBjb250ZXh0XCJcbiAqIEBwYXJhbSB7c3RyaW5nfSBjb21wb25lbnROYW1lIE5hbWUgb2YgdGhlIGNvbXBvbmVudCBmb3IgZXJyb3IgbWVzc2FnZXMuXG4gKiBAcGFyYW0gez9GdW5jdGlvbn0gZ2V0U3RhY2sgUmV0dXJucyB0aGUgY29tcG9uZW50IHN0YWNrLlxuICogQHByaXZhdGVcbiAqL1xuZnVuY3Rpb24gY2hlY2tQcm9wVHlwZXModHlwZVNwZWNzLCB2YWx1ZXMsIGxvY2F0aW9uLCBjb21wb25lbnROYW1lLCBnZXRTdGFjaykge1xuICBpZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09ICdwcm9kdWN0aW9uJykge1xuICAgIGZvciAodmFyIHR5cGVTcGVjTmFtZSBpbiB0eXBlU3BlY3MpIHtcbiAgICAgIGlmIChoYXModHlwZVNwZWNzLCB0eXBlU3BlY05hbWUpKSB7XG4gICAgICAgIHZhciBlcnJvcjtcbiAgICAgICAgLy8gUHJvcCB0eXBlIHZhbGlkYXRpb24gbWF5IHRocm93LiBJbiBjYXNlIHRoZXkgZG8sIHdlIGRvbid0IHdhbnQgdG9cbiAgICAgICAgLy8gZmFpbCB0aGUgcmVuZGVyIHBoYXNlIHdoZXJlIGl0IGRpZG4ndCBmYWlsIGJlZm9yZS4gU28gd2UgbG9nIGl0LlxuICAgICAgICAvLyBBZnRlciB0aGVzZSBoYXZlIGJlZW4gY2xlYW5lZCB1cCwgd2UnbGwgbGV0IHRoZW0gdGhyb3cuXG4gICAgICAgIHRyeSB7XG4gICAgICAgICAgLy8gVGhpcyBpcyBpbnRlbnRpb25hbGx5IGFuIGludmFyaWFudCB0aGF0IGdldHMgY2F1Z2h0LiBJdCdzIHRoZSBzYW1lXG4gICAgICAgICAgLy8gYmVoYXZpb3IgYXMgd2l0aG91dCB0aGlzIHN0YXRlbWVudCBleGNlcHQgd2l0aCBhIGJldHRlciBtZXNzYWdlLlxuICAgICAgICAgIGlmICh0eXBlb2YgdHlwZVNwZWNzW3R5cGVTcGVjTmFtZV0gIT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgICAgIHZhciBlcnIgPSBFcnJvcihcbiAgICAgICAgICAgICAgKGNvbXBvbmVudE5hbWUgfHwgJ1JlYWN0IGNsYXNzJykgKyAnOiAnICsgbG9jYXRpb24gKyAnIHR5cGUgYCcgKyB0eXBlU3BlY05hbWUgKyAnYCBpcyBpbnZhbGlkOyAnICtcbiAgICAgICAgICAgICAgJ2l0IG11c3QgYmUgYSBmdW5jdGlvbiwgdXN1YWxseSBmcm9tIHRoZSBgcHJvcC10eXBlc2AgcGFja2FnZSwgYnV0IHJlY2VpdmVkIGAnICsgdHlwZW9mIHR5cGVTcGVjc1t0eXBlU3BlY05hbWVdICsgJ2AuJyArXG4gICAgICAgICAgICAgICdUaGlzIG9mdGVuIGhhcHBlbnMgYmVjYXVzZSBvZiB0eXBvcyBzdWNoIGFzIGBQcm9wVHlwZXMuZnVuY3Rpb25gIGluc3RlYWQgb2YgYFByb3BUeXBlcy5mdW5jYC4nXG4gICAgICAgICAgICApO1xuICAgICAgICAgICAgZXJyLm5hbWUgPSAnSW52YXJpYW50IFZpb2xhdGlvbic7XG4gICAgICAgICAgICB0aHJvdyBlcnI7XG4gICAgICAgICAgfVxuICAgICAgICAgIGVycm9yID0gdHlwZVNwZWNzW3R5cGVTcGVjTmFtZV0odmFsdWVzLCB0eXBlU3BlY05hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBudWxsLCBSZWFjdFByb3BUeXBlc1NlY3JldCk7XG4gICAgICAgIH0gY2F0Y2ggKGV4KSB7XG4gICAgICAgICAgZXJyb3IgPSBleDtcbiAgICAgICAgfVxuICAgICAgICBpZiAoZXJyb3IgJiYgIShlcnJvciBpbnN0YW5jZW9mIEVycm9yKSkge1xuICAgICAgICAgIHByaW50V2FybmluZyhcbiAgICAgICAgICAgIChjb21wb25lbnROYW1lIHx8ICdSZWFjdCBjbGFzcycpICsgJzogdHlwZSBzcGVjaWZpY2F0aW9uIG9mICcgK1xuICAgICAgICAgICAgbG9jYXRpb24gKyAnIGAnICsgdHlwZVNwZWNOYW1lICsgJ2AgaXMgaW52YWxpZDsgdGhlIHR5cGUgY2hlY2tlciAnICtcbiAgICAgICAgICAgICdmdW5jdGlvbiBtdXN0IHJldHVybiBgbnVsbGAgb3IgYW4gYEVycm9yYCBidXQgcmV0dXJuZWQgYSAnICsgdHlwZW9mIGVycm9yICsgJy4gJyArXG4gICAgICAgICAgICAnWW91IG1heSBoYXZlIGZvcmdvdHRlbiB0byBwYXNzIGFuIGFyZ3VtZW50IHRvIHRoZSB0eXBlIGNoZWNrZXIgJyArXG4gICAgICAgICAgICAnY3JlYXRvciAoYXJyYXlPZiwgaW5zdGFuY2VPZiwgb2JqZWN0T2YsIG9uZU9mLCBvbmVPZlR5cGUsIGFuZCAnICtcbiAgICAgICAgICAgICdzaGFwZSBhbGwgcmVxdWlyZSBhbiBhcmd1bWVudCkuJ1xuICAgICAgICAgICk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKGVycm9yIGluc3RhbmNlb2YgRXJyb3IgJiYgIShlcnJvci5tZXNzYWdlIGluIGxvZ2dlZFR5cGVGYWlsdXJlcykpIHtcbiAgICAgICAgICAvLyBPbmx5IG1vbml0b3IgdGhpcyBmYWlsdXJlIG9uY2UgYmVjYXVzZSB0aGVyZSB0ZW5kcyB0byBiZSBhIGxvdCBvZiB0aGVcbiAgICAgICAgICAvLyBzYW1lIGVycm9yLlxuICAgICAgICAgIGxvZ2dlZFR5cGVGYWlsdXJlc1tlcnJvci5tZXNzYWdlXSA9IHRydWU7XG5cbiAgICAgICAgICB2YXIgc3RhY2sgPSBnZXRTdGFjayA/IGdldFN0YWNrKCkgOiAnJztcblxuICAgICAgICAgIHByaW50V2FybmluZyhcbiAgICAgICAgICAgICdGYWlsZWQgJyArIGxvY2F0aW9uICsgJyB0eXBlOiAnICsgZXJyb3IubWVzc2FnZSArIChzdGFjayAhPSBudWxsID8gc3RhY2sgOiAnJylcbiAgICAgICAgICApO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgfVxuICB9XG59XG5cbi8qKlxuICogUmVzZXRzIHdhcm5pbmcgY2FjaGUgd2hlbiB0ZXN0aW5nLlxuICpcbiAqIEBwcml2YXRlXG4gKi9cbmNoZWNrUHJvcFR5cGVzLnJlc2V0V2FybmluZ0NhY2hlID0gZnVuY3Rpb24oKSB7XG4gIGlmIChwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gJ3Byb2R1Y3Rpb24nKSB7XG4gICAgbG9nZ2VkVHlwZUZhaWx1cmVzID0ge307XG4gIH1cbn1cblxubW9kdWxlLmV4cG9ydHMgPSBjaGVja1Byb3BUeXBlcztcbiIsIi8qKlxuICogQ29weXJpZ2h0IChjKSAyMDEzLXByZXNlbnQsIEZhY2Vib29rLCBJbmMuXG4gKlxuICogVGhpcyBzb3VyY2UgY29kZSBpcyBsaWNlbnNlZCB1bmRlciB0aGUgTUlUIGxpY2Vuc2UgZm91bmQgaW4gdGhlXG4gKiBMSUNFTlNFIGZpbGUgaW4gdGhlIHJvb3QgZGlyZWN0b3J5IG9mIHRoaXMgc291cmNlIHRyZWUuXG4gKi9cblxuJ3VzZSBzdHJpY3QnO1xuXG52YXIgUmVhY3RJcyA9IHJlcXVpcmUoJ3JlYWN0LWlzJyk7XG52YXIgYXNzaWduID0gcmVxdWlyZSgnb2JqZWN0LWFzc2lnbicpO1xuXG52YXIgUmVhY3RQcm9wVHlwZXNTZWNyZXQgPSByZXF1aXJlKCcuL2xpYi9SZWFjdFByb3BUeXBlc1NlY3JldCcpO1xudmFyIGhhcyA9IHJlcXVpcmUoJy4vbGliL2hhcycpO1xudmFyIGNoZWNrUHJvcFR5cGVzID0gcmVxdWlyZSgnLi9jaGVja1Byb3BUeXBlcycpO1xuXG52YXIgcHJpbnRXYXJuaW5nID0gZnVuY3Rpb24oKSB7fTtcblxuaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicpIHtcbiAgcHJpbnRXYXJuaW5nID0gZnVuY3Rpb24odGV4dCkge1xuICAgIHZhciBtZXNzYWdlID0gJ1dhcm5pbmc6ICcgKyB0ZXh0O1xuICAgIGlmICh0eXBlb2YgY29uc29sZSAhPT0gJ3VuZGVmaW5lZCcpIHtcbiAgICAgIGNvbnNvbGUuZXJyb3IobWVzc2FnZSk7XG4gICAgfVxuICAgIHRyeSB7XG4gICAgICAvLyAtLS0gV2VsY29tZSB0byBkZWJ1Z2dpbmcgUmVhY3QgLS0tXG4gICAgICAvLyBUaGlzIGVycm9yIHdhcyB0aHJvd24gYXMgYSBjb252ZW5pZW5jZSBzbyB0aGF0IHlvdSBjYW4gdXNlIHRoaXMgc3RhY2tcbiAgICAgIC8vIHRvIGZpbmQgdGhlIGNhbGxzaXRlIHRoYXQgY2F1c2VkIHRoaXMgd2FybmluZyB0byBmaXJlLlxuICAgICAgdGhyb3cgbmV3IEVycm9yKG1lc3NhZ2UpO1xuICAgIH0gY2F0Y2ggKHgpIHt9XG4gIH07XG59XG5cbmZ1bmN0aW9uIGVtcHR5RnVuY3Rpb25UaGF0UmV0dXJuc051bGwoKSB7XG4gIHJldHVybiBudWxsO1xufVxuXG5tb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uKGlzVmFsaWRFbGVtZW50LCB0aHJvd09uRGlyZWN0QWNjZXNzKSB7XG4gIC8qIGdsb2JhbCBTeW1ib2wgKi9cbiAgdmFyIElURVJBVE9SX1NZTUJPTCA9IHR5cGVvZiBTeW1ib2wgPT09ICdmdW5jdGlvbicgJiYgU3ltYm9sLml0ZXJhdG9yO1xuICB2YXIgRkFVWF9JVEVSQVRPUl9TWU1CT0wgPSAnQEBpdGVyYXRvcic7IC8vIEJlZm9yZSBTeW1ib2wgc3BlYy5cblxuICAvKipcbiAgICogUmV0dXJucyB0aGUgaXRlcmF0b3IgbWV0aG9kIGZ1bmN0aW9uIGNvbnRhaW5lZCBvbiB0aGUgaXRlcmFibGUgb2JqZWN0LlxuICAgKlxuICAgKiBCZSBzdXJlIHRvIGludm9rZSB0aGUgZnVuY3Rpb24gd2l0aCB0aGUgaXRlcmFibGUgYXMgY29udGV4dDpcbiAgICpcbiAgICogICAgIHZhciBpdGVyYXRvckZuID0gZ2V0SXRlcmF0b3JGbihteUl0ZXJhYmxlKTtcbiAgICogICAgIGlmIChpdGVyYXRvckZuKSB7XG4gICAqICAgICAgIHZhciBpdGVyYXRvciA9IGl0ZXJhdG9yRm4uY2FsbChteUl0ZXJhYmxlKTtcbiAgICogICAgICAgLi4uXG4gICAqICAgICB9XG4gICAqXG4gICAqIEBwYXJhbSB7P29iamVjdH0gbWF5YmVJdGVyYWJsZVxuICAgKiBAcmV0dXJuIHs/ZnVuY3Rpb259XG4gICAqL1xuICBmdW5jdGlvbiBnZXRJdGVyYXRvckZuKG1heWJlSXRlcmFibGUpIHtcbiAgICB2YXIgaXRlcmF0b3JGbiA9IG1heWJlSXRlcmFibGUgJiYgKElURVJBVE9SX1NZTUJPTCAmJiBtYXliZUl0ZXJhYmxlW0lURVJBVE9SX1NZTUJPTF0gfHwgbWF5YmVJdGVyYWJsZVtGQVVYX0lURVJBVE9SX1NZTUJPTF0pO1xuICAgIGlmICh0eXBlb2YgaXRlcmF0b3JGbiA9PT0gJ2Z1bmN0aW9uJykge1xuICAgICAgcmV0dXJuIGl0ZXJhdG9yRm47XG4gICAgfVxuICB9XG5cbiAgLyoqXG4gICAqIENvbGxlY3Rpb24gb2YgbWV0aG9kcyB0aGF0IGFsbG93IGRlY2xhcmF0aW9uIGFuZCB2YWxpZGF0aW9uIG9mIHByb3BzIHRoYXQgYXJlXG4gICAqIHN1cHBsaWVkIHRvIFJlYWN0IGNvbXBvbmVudHMuIEV4YW1wbGUgdXNhZ2U6XG4gICAqXG4gICAqICAgdmFyIFByb3BzID0gcmVxdWlyZSgnUmVhY3RQcm9wVHlwZXMnKTtcbiAgICogICB2YXIgTXlBcnRpY2xlID0gUmVhY3QuY3JlYXRlQ2xhc3Moe1xuICAgKiAgICAgcHJvcFR5cGVzOiB7XG4gICAqICAgICAgIC8vIEFuIG9wdGlvbmFsIHN0cmluZyBwcm9wIG5hbWVkIFwiZGVzY3JpcHRpb25cIi5cbiAgICogICAgICAgZGVzY3JpcHRpb246IFByb3BzLnN0cmluZyxcbiAgICpcbiAgICogICAgICAgLy8gQSByZXF1aXJlZCBlbnVtIHByb3AgbmFtZWQgXCJjYXRlZ29yeVwiLlxuICAgKiAgICAgICBjYXRlZ29yeTogUHJvcHMub25lT2YoWydOZXdzJywnUGhvdG9zJ10pLmlzUmVxdWlyZWQsXG4gICAqXG4gICAqICAgICAgIC8vIEEgcHJvcCBuYW1lZCBcImRpYWxvZ1wiIHRoYXQgcmVxdWlyZXMgYW4gaW5zdGFuY2Ugb2YgRGlhbG9nLlxuICAgKiAgICAgICBkaWFsb2c6IFByb3BzLmluc3RhbmNlT2YoRGlhbG9nKS5pc1JlcXVpcmVkXG4gICAqICAgICB9LFxuICAgKiAgICAgcmVuZGVyOiBmdW5jdGlvbigpIHsgLi4uIH1cbiAgICogICB9KTtcbiAgICpcbiAgICogQSBtb3JlIGZvcm1hbCBzcGVjaWZpY2F0aW9uIG9mIGhvdyB0aGVzZSBtZXRob2RzIGFyZSB1c2VkOlxuICAgKlxuICAgKiAgIHR5cGUgOj0gYXJyYXl8Ym9vbHxmdW5jfG9iamVjdHxudW1iZXJ8c3RyaW5nfG9uZU9mKFsuLi5dKXxpbnN0YW5jZU9mKC4uLilcbiAgICogICBkZWNsIDo9IFJlYWN0UHJvcFR5cGVzLnt0eXBlfSguaXNSZXF1aXJlZCk/XG4gICAqXG4gICAqIEVhY2ggYW5kIGV2ZXJ5IGRlY2xhcmF0aW9uIHByb2R1Y2VzIGEgZnVuY3Rpb24gd2l0aCB0aGUgc2FtZSBzaWduYXR1cmUuIFRoaXNcbiAgICogYWxsb3dzIHRoZSBjcmVhdGlvbiBvZiBjdXN0b20gdmFsaWRhdGlvbiBmdW5jdGlvbnMuIEZvciBleGFtcGxlOlxuICAgKlxuICAgKiAgdmFyIE15TGluayA9IFJlYWN0LmNyZWF0ZUNsYXNzKHtcbiAgICogICAgcHJvcFR5cGVzOiB7XG4gICAqICAgICAgLy8gQW4gb3B0aW9uYWwgc3RyaW5nIG9yIFVSSSBwcm9wIG5hbWVkIFwiaHJlZlwiLlxuICAgKiAgICAgIGhyZWY6IGZ1bmN0aW9uKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSkge1xuICAgKiAgICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICogICAgICAgIGlmIChwcm9wVmFsdWUgIT0gbnVsbCAmJiB0eXBlb2YgcHJvcFZhbHVlICE9PSAnc3RyaW5nJyAmJlxuICAgKiAgICAgICAgICAgICEocHJvcFZhbHVlIGluc3RhbmNlb2YgVVJJKSkge1xuICAgKiAgICAgICAgICByZXR1cm4gbmV3IEVycm9yKFxuICAgKiAgICAgICAgICAgICdFeHBlY3RlZCBhIHN0cmluZyBvciBhbiBVUkkgZm9yICcgKyBwcm9wTmFtZSArICcgaW4gJyArXG4gICAqICAgICAgICAgICAgY29tcG9uZW50TmFtZVxuICAgKiAgICAgICAgICApO1xuICAgKiAgICAgICAgfVxuICAgKiAgICAgIH1cbiAgICogICAgfSxcbiAgICogICAgcmVuZGVyOiBmdW5jdGlvbigpIHsuLi59XG4gICAqICB9KTtcbiAgICpcbiAgICogQGludGVybmFsXG4gICAqL1xuXG4gIHZhciBBTk9OWU1PVVMgPSAnPDxhbm9ueW1vdXM+Pic7XG5cbiAgLy8gSW1wb3J0YW50IVxuICAvLyBLZWVwIHRoaXMgbGlzdCBpbiBzeW5jIHdpdGggcHJvZHVjdGlvbiB2ZXJzaW9uIGluIGAuL2ZhY3RvcnlXaXRoVGhyb3dpbmdTaGltcy5qc2AuXG4gIHZhciBSZWFjdFByb3BUeXBlcyA9IHtcbiAgICBhcnJheTogY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIoJ2FycmF5JyksXG4gICAgYmlnaW50OiBjcmVhdGVQcmltaXRpdmVUeXBlQ2hlY2tlcignYmlnaW50JyksXG4gICAgYm9vbDogY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIoJ2Jvb2xlYW4nKSxcbiAgICBmdW5jOiBjcmVhdGVQcmltaXRpdmVUeXBlQ2hlY2tlcignZnVuY3Rpb24nKSxcbiAgICBudW1iZXI6IGNyZWF0ZVByaW1pdGl2ZVR5cGVDaGVja2VyKCdudW1iZXInKSxcbiAgICBvYmplY3Q6IGNyZWF0ZVByaW1pdGl2ZVR5cGVDaGVja2VyKCdvYmplY3QnKSxcbiAgICBzdHJpbmc6IGNyZWF0ZVByaW1pdGl2ZVR5cGVDaGVja2VyKCdzdHJpbmcnKSxcbiAgICBzeW1ib2w6IGNyZWF0ZVByaW1pdGl2ZVR5cGVDaGVja2VyKCdzeW1ib2wnKSxcblxuICAgIGFueTogY3JlYXRlQW55VHlwZUNoZWNrZXIoKSxcbiAgICBhcnJheU9mOiBjcmVhdGVBcnJheU9mVHlwZUNoZWNrZXIsXG4gICAgZWxlbWVudDogY3JlYXRlRWxlbWVudFR5cGVDaGVja2VyKCksXG4gICAgZWxlbWVudFR5cGU6IGNyZWF0ZUVsZW1lbnRUeXBlVHlwZUNoZWNrZXIoKSxcbiAgICBpbnN0YW5jZU9mOiBjcmVhdGVJbnN0YW5jZVR5cGVDaGVja2VyLFxuICAgIG5vZGU6IGNyZWF0ZU5vZGVDaGVja2VyKCksXG4gICAgb2JqZWN0T2Y6IGNyZWF0ZU9iamVjdE9mVHlwZUNoZWNrZXIsXG4gICAgb25lT2Y6IGNyZWF0ZUVudW1UeXBlQ2hlY2tlcixcbiAgICBvbmVPZlR5cGU6IGNyZWF0ZVVuaW9uVHlwZUNoZWNrZXIsXG4gICAgc2hhcGU6IGNyZWF0ZVNoYXBlVHlwZUNoZWNrZXIsXG4gICAgZXhhY3Q6IGNyZWF0ZVN0cmljdFNoYXBlVHlwZUNoZWNrZXIsXG4gIH07XG5cbiAgLyoqXG4gICAqIGlubGluZWQgT2JqZWN0LmlzIHBvbHlmaWxsIHRvIGF2b2lkIHJlcXVpcmluZyBjb25zdW1lcnMgc2hpcCB0aGVpciBvd25cbiAgICogaHR0cHM6Ly9kZXZlbG9wZXIubW96aWxsYS5vcmcvZW4tVVMvZG9jcy9XZWIvSmF2YVNjcmlwdC9SZWZlcmVuY2UvR2xvYmFsX09iamVjdHMvT2JqZWN0L2lzXG4gICAqL1xuICAvKmVzbGludC1kaXNhYmxlIG5vLXNlbGYtY29tcGFyZSovXG4gIGZ1bmN0aW9uIGlzKHgsIHkpIHtcbiAgICAvLyBTYW1lVmFsdWUgYWxnb3JpdGhtXG4gICAgaWYgKHggPT09IHkpIHtcbiAgICAgIC8vIFN0ZXBzIDEtNSwgNy0xMFxuICAgICAgLy8gU3RlcHMgNi5iLTYuZTogKzAgIT0gLTBcbiAgICAgIHJldHVybiB4ICE9PSAwIHx8IDEgLyB4ID09PSAxIC8geTtcbiAgICB9IGVsc2Uge1xuICAgICAgLy8gU3RlcCA2LmE6IE5hTiA9PSBOYU5cbiAgICAgIHJldHVybiB4ICE9PSB4ICYmIHkgIT09IHk7XG4gICAgfVxuICB9XG4gIC8qZXNsaW50LWVuYWJsZSBuby1zZWxmLWNvbXBhcmUqL1xuXG4gIC8qKlxuICAgKiBXZSB1c2UgYW4gRXJyb3ItbGlrZSBvYmplY3QgZm9yIGJhY2t3YXJkIGNvbXBhdGliaWxpdHkgYXMgcGVvcGxlIG1heSBjYWxsXG4gICAqIFByb3BUeXBlcyBkaXJlY3RseSBhbmQgaW5zcGVjdCB0aGVpciBvdXRwdXQuIEhvd2V2ZXIsIHdlIGRvbid0IHVzZSByZWFsXG4gICAqIEVycm9ycyBhbnltb3JlLiBXZSBkb24ndCBpbnNwZWN0IHRoZWlyIHN0YWNrIGFueXdheSwgYW5kIGNyZWF0aW5nIHRoZW1cbiAgICogaXMgcHJvaGliaXRpdmVseSBleHBlbnNpdmUgaWYgdGhleSBhcmUgY3JlYXRlZCB0b28gb2Z0ZW4sIHN1Y2ggYXMgd2hhdFxuICAgKiBoYXBwZW5zIGluIG9uZU9mVHlwZSgpIGZvciBhbnkgdHlwZSBiZWZvcmUgdGhlIG9uZSB0aGF0IG1hdGNoZWQuXG4gICAqL1xuICBmdW5jdGlvbiBQcm9wVHlwZUVycm9yKG1lc3NhZ2UsIGRhdGEpIHtcbiAgICB0aGlzLm1lc3NhZ2UgPSBtZXNzYWdlO1xuICAgIHRoaXMuZGF0YSA9IGRhdGEgJiYgdHlwZW9mIGRhdGEgPT09ICdvYmplY3QnID8gZGF0YToge307XG4gICAgdGhpcy5zdGFjayA9ICcnO1xuICB9XG4gIC8vIE1ha2UgYGluc3RhbmNlb2YgRXJyb3JgIHN0aWxsIHdvcmsgZm9yIHJldHVybmVkIGVycm9ycy5cbiAgUHJvcFR5cGVFcnJvci5wcm90b3R5cGUgPSBFcnJvci5wcm90b3R5cGU7XG5cbiAgZnVuY3Rpb24gY3JlYXRlQ2hhaW5hYmxlVHlwZUNoZWNrZXIodmFsaWRhdGUpIHtcbiAgICBpZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09ICdwcm9kdWN0aW9uJykge1xuICAgICAgdmFyIG1hbnVhbFByb3BUeXBlQ2FsbENhY2hlID0ge307XG4gICAgICB2YXIgbWFudWFsUHJvcFR5cGVXYXJuaW5nQ291bnQgPSAwO1xuICAgIH1cbiAgICBmdW5jdGlvbiBjaGVja1R5cGUoaXNSZXF1aXJlZCwgcHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lLCBzZWNyZXQpIHtcbiAgICAgIGNvbXBvbmVudE5hbWUgPSBjb21wb25lbnROYW1lIHx8IEFOT05ZTU9VUztcbiAgICAgIHByb3BGdWxsTmFtZSA9IHByb3BGdWxsTmFtZSB8fCBwcm9wTmFtZTtcblxuICAgICAgaWYgKHNlY3JldCAhPT0gUmVhY3RQcm9wVHlwZXNTZWNyZXQpIHtcbiAgICAgICAgaWYgKHRocm93T25EaXJlY3RBY2Nlc3MpIHtcbiAgICAgICAgICAvLyBOZXcgYmVoYXZpb3Igb25seSBmb3IgdXNlcnMgb2YgYHByb3AtdHlwZXNgIHBhY2thZ2VcbiAgICAgICAgICB2YXIgZXJyID0gbmV3IEVycm9yKFxuICAgICAgICAgICAgJ0NhbGxpbmcgUHJvcFR5cGVzIHZhbGlkYXRvcnMgZGlyZWN0bHkgaXMgbm90IHN1cHBvcnRlZCBieSB0aGUgYHByb3AtdHlwZXNgIHBhY2thZ2UuICcgK1xuICAgICAgICAgICAgJ1VzZSBgUHJvcFR5cGVzLmNoZWNrUHJvcFR5cGVzKClgIHRvIGNhbGwgdGhlbS4gJyArXG4gICAgICAgICAgICAnUmVhZCBtb3JlIGF0IGh0dHA6Ly9mYi5tZS91c2UtY2hlY2stcHJvcC10eXBlcydcbiAgICAgICAgICApO1xuICAgICAgICAgIGVyci5uYW1lID0gJ0ludmFyaWFudCBWaW9sYXRpb24nO1xuICAgICAgICAgIHRocm93IGVycjtcbiAgICAgICAgfSBlbHNlIGlmIChwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gJ3Byb2R1Y3Rpb24nICYmIHR5cGVvZiBjb25zb2xlICE9PSAndW5kZWZpbmVkJykge1xuICAgICAgICAgIC8vIE9sZCBiZWhhdmlvciBmb3IgcGVvcGxlIHVzaW5nIFJlYWN0LlByb3BUeXBlc1xuICAgICAgICAgIHZhciBjYWNoZUtleSA9IGNvbXBvbmVudE5hbWUgKyAnOicgKyBwcm9wTmFtZTtcbiAgICAgICAgICBpZiAoXG4gICAgICAgICAgICAhbWFudWFsUHJvcFR5cGVDYWxsQ2FjaGVbY2FjaGVLZXldICYmXG4gICAgICAgICAgICAvLyBBdm9pZCBzcGFtbWluZyB0aGUgY29uc29sZSBiZWNhdXNlIHRoZXkgYXJlIG9mdGVuIG5vdCBhY3Rpb25hYmxlIGV4Y2VwdCBmb3IgbGliIGF1dGhvcnNcbiAgICAgICAgICAgIG1hbnVhbFByb3BUeXBlV2FybmluZ0NvdW50IDwgM1xuICAgICAgICAgICkge1xuICAgICAgICAgICAgcHJpbnRXYXJuaW5nKFxuICAgICAgICAgICAgICAnWW91IGFyZSBtYW51YWxseSBjYWxsaW5nIGEgUmVhY3QuUHJvcFR5cGVzIHZhbGlkYXRpb24gJyArXG4gICAgICAgICAgICAgICdmdW5jdGlvbiBmb3IgdGhlIGAnICsgcHJvcEZ1bGxOYW1lICsgJ2AgcHJvcCBvbiBgJyArIGNvbXBvbmVudE5hbWUgKyAnYC4gVGhpcyBpcyBkZXByZWNhdGVkICcgK1xuICAgICAgICAgICAgICAnYW5kIHdpbGwgdGhyb3cgaW4gdGhlIHN0YW5kYWxvbmUgYHByb3AtdHlwZXNgIHBhY2thZ2UuICcgK1xuICAgICAgICAgICAgICAnWW91IG1heSBiZSBzZWVpbmcgdGhpcyB3YXJuaW5nIGR1ZSB0byBhIHRoaXJkLXBhcnR5IFByb3BUeXBlcyAnICtcbiAgICAgICAgICAgICAgJ2xpYnJhcnkuIFNlZSBodHRwczovL2ZiLm1lL3JlYWN0LXdhcm5pbmctZG9udC1jYWxsLXByb3B0eXBlcyAnICsgJ2ZvciBkZXRhaWxzLidcbiAgICAgICAgICAgICk7XG4gICAgICAgICAgICBtYW51YWxQcm9wVHlwZUNhbGxDYWNoZVtjYWNoZUtleV0gPSB0cnVlO1xuICAgICAgICAgICAgbWFudWFsUHJvcFR5cGVXYXJuaW5nQ291bnQrKztcbiAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIGlmIChwcm9wc1twcm9wTmFtZV0gPT0gbnVsbCkge1xuICAgICAgICBpZiAoaXNSZXF1aXJlZCkge1xuICAgICAgICAgIGlmIChwcm9wc1twcm9wTmFtZV0gPT09IG51bGwpIHtcbiAgICAgICAgICAgIHJldHVybiBuZXcgUHJvcFR5cGVFcnJvcignVGhlICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBpcyBtYXJrZWQgYXMgcmVxdWlyZWQgJyArICgnaW4gYCcgKyBjb21wb25lbnROYW1lICsgJ2AsIGJ1dCBpdHMgdmFsdWUgaXMgYG51bGxgLicpKTtcbiAgICAgICAgICB9XG4gICAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdUaGUgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIGlzIG1hcmtlZCBhcyByZXF1aXJlZCBpbiAnICsgKCdgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgYnV0IGl0cyB2YWx1ZSBpcyBgdW5kZWZpbmVkYC4nKSk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICByZXR1cm4gdmFsaWRhdGUocHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lKTtcbiAgICAgIH1cbiAgICB9XG5cbiAgICB2YXIgY2hhaW5lZENoZWNrVHlwZSA9IGNoZWNrVHlwZS5iaW5kKG51bGwsIGZhbHNlKTtcbiAgICBjaGFpbmVkQ2hlY2tUeXBlLmlzUmVxdWlyZWQgPSBjaGVja1R5cGUuYmluZChudWxsLCB0cnVlKTtcblxuICAgIHJldHVybiBjaGFpbmVkQ2hlY2tUeXBlO1xuICB9XG5cbiAgZnVuY3Rpb24gY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIoZXhwZWN0ZWRUeXBlKSB7XG4gICAgZnVuY3Rpb24gdmFsaWRhdGUocHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lLCBzZWNyZXQpIHtcbiAgICAgIHZhciBwcm9wVmFsdWUgPSBwcm9wc1twcm9wTmFtZV07XG4gICAgICB2YXIgcHJvcFR5cGUgPSBnZXRQcm9wVHlwZShwcm9wVmFsdWUpO1xuICAgICAgaWYgKHByb3BUeXBlICE9PSBleHBlY3RlZFR5cGUpIHtcbiAgICAgICAgLy8gYHByb3BWYWx1ZWAgYmVpbmcgaW5zdGFuY2Ugb2YsIHNheSwgZGF0ZS9yZWdleHAsIHBhc3MgdGhlICdvYmplY3QnXG4gICAgICAgIC8vIGNoZWNrLCBidXQgd2UgY2FuIG9mZmVyIGEgbW9yZSBwcmVjaXNlIGVycm9yIG1lc3NhZ2UgaGVyZSByYXRoZXIgdGhhblxuICAgICAgICAvLyAnb2YgdHlwZSBgb2JqZWN0YCcuXG4gICAgICAgIHZhciBwcmVjaXNlVHlwZSA9IGdldFByZWNpc2VUeXBlKHByb3BWYWx1ZSk7XG5cbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKFxuICAgICAgICAgICdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiB0eXBlICcgKyAoJ2AnICsgcHJlY2lzZVR5cGUgKyAnYCBzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgJykgKyAoJ2AnICsgZXhwZWN0ZWRUeXBlICsgJ2AuJyksXG4gICAgICAgICAge2V4cGVjdGVkVHlwZTogZXhwZWN0ZWRUeXBlfVxuICAgICAgICApO1xuICAgICAgfVxuICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSk7XG4gIH1cblxuICBmdW5jdGlvbiBjcmVhdGVBbnlUeXBlQ2hlY2tlcigpIHtcbiAgICByZXR1cm4gY3JlYXRlQ2hhaW5hYmxlVHlwZUNoZWNrZXIoZW1wdHlGdW5jdGlvblRoYXRSZXR1cm5zTnVsbCk7XG4gIH1cblxuICBmdW5jdGlvbiBjcmVhdGVBcnJheU9mVHlwZUNoZWNrZXIodHlwZUNoZWNrZXIpIHtcbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpIHtcbiAgICAgIGlmICh0eXBlb2YgdHlwZUNoZWNrZXIgIT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdQcm9wZXJ0eSBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIGNvbXBvbmVudCBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCBoYXMgaW52YWxpZCBQcm9wVHlwZSBub3RhdGlvbiBpbnNpZGUgYXJyYXlPZi4nKTtcbiAgICAgIH1cbiAgICAgIHZhciBwcm9wVmFsdWUgPSBwcm9wc1twcm9wTmFtZV07XG4gICAgICBpZiAoIUFycmF5LmlzQXJyYXkocHJvcFZhbHVlKSkge1xuICAgICAgICB2YXIgcHJvcFR5cGUgPSBnZXRQcm9wVHlwZShwcm9wVmFsdWUpO1xuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIHR5cGUgJyArICgnYCcgKyBwcm9wVHlwZSArICdgIHN1cHBsaWVkIHRvIGAnICsgY29tcG9uZW50TmFtZSArICdgLCBleHBlY3RlZCBhbiBhcnJheS4nKSk7XG4gICAgICB9XG4gICAgICBmb3IgKHZhciBpID0gMDsgaSA8IHByb3BWYWx1ZS5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgZXJyb3IgPSB0eXBlQ2hlY2tlcihwcm9wVmFsdWUsIGksIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUgKyAnWycgKyBpICsgJ10nLCBSZWFjdFByb3BUeXBlc1NlY3JldCk7XG4gICAgICAgIGlmIChlcnJvciBpbnN0YW5jZW9mIEVycm9yKSB7XG4gICAgICAgICAgcmV0dXJuIGVycm9yO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZUVsZW1lbnRUeXBlQ2hlY2tlcigpIHtcbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpIHtcbiAgICAgIHZhciBwcm9wVmFsdWUgPSBwcm9wc1twcm9wTmFtZV07XG4gICAgICBpZiAoIWlzVmFsaWRFbGVtZW50KHByb3BWYWx1ZSkpIHtcbiAgICAgICAgdmFyIHByb3BUeXBlID0gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKTtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiB0eXBlICcgKyAoJ2AnICsgcHJvcFR5cGUgKyAnYCBzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgYSBzaW5nbGUgUmVhY3RFbGVtZW50LicpKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbiAgICByZXR1cm4gY3JlYXRlQ2hhaW5hYmxlVHlwZUNoZWNrZXIodmFsaWRhdGUpO1xuICB9XG5cbiAgZnVuY3Rpb24gY3JlYXRlRWxlbWVudFR5cGVUeXBlQ2hlY2tlcigpIHtcbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpIHtcbiAgICAgIHZhciBwcm9wVmFsdWUgPSBwcm9wc1twcm9wTmFtZV07XG4gICAgICBpZiAoIVJlYWN0SXMuaXNWYWxpZEVsZW1lbnRUeXBlKHByb3BWYWx1ZSkpIHtcbiAgICAgICAgdmFyIHByb3BUeXBlID0gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKTtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiB0eXBlICcgKyAoJ2AnICsgcHJvcFR5cGUgKyAnYCBzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgYSBzaW5nbGUgUmVhY3RFbGVtZW50IHR5cGUuJykpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSk7XG4gIH1cblxuICBmdW5jdGlvbiBjcmVhdGVJbnN0YW5jZVR5cGVDaGVja2VyKGV4cGVjdGVkQ2xhc3MpIHtcbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpIHtcbiAgICAgIGlmICghKHByb3BzW3Byb3BOYW1lXSBpbnN0YW5jZW9mIGV4cGVjdGVkQ2xhc3MpKSB7XG4gICAgICAgIHZhciBleHBlY3RlZENsYXNzTmFtZSA9IGV4cGVjdGVkQ2xhc3MubmFtZSB8fCBBTk9OWU1PVVM7XG4gICAgICAgIHZhciBhY3R1YWxDbGFzc05hbWUgPSBnZXRDbGFzc05hbWUocHJvcHNbcHJvcE5hbWVdKTtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiB0eXBlICcgKyAoJ2AnICsgYWN0dWFsQ2xhc3NOYW1lICsgJ2Agc3VwcGxpZWQgdG8gYCcgKyBjb21wb25lbnROYW1lICsgJ2AsIGV4cGVjdGVkICcpICsgKCdpbnN0YW5jZSBvZiBgJyArIGV4cGVjdGVkQ2xhc3NOYW1lICsgJ2AuJykpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSk7XG4gIH1cblxuICBmdW5jdGlvbiBjcmVhdGVFbnVtVHlwZUNoZWNrZXIoZXhwZWN0ZWRWYWx1ZXMpIHtcbiAgICBpZiAoIUFycmF5LmlzQXJyYXkoZXhwZWN0ZWRWYWx1ZXMpKSB7XG4gICAgICBpZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09ICdwcm9kdWN0aW9uJykge1xuICAgICAgICBpZiAoYXJndW1lbnRzLmxlbmd0aCA+IDEpIHtcbiAgICAgICAgICBwcmludFdhcm5pbmcoXG4gICAgICAgICAgICAnSW52YWxpZCBhcmd1bWVudHMgc3VwcGxpZWQgdG8gb25lT2YsIGV4cGVjdGVkIGFuIGFycmF5LCBnb3QgJyArIGFyZ3VtZW50cy5sZW5ndGggKyAnIGFyZ3VtZW50cy4gJyArXG4gICAgICAgICAgICAnQSBjb21tb24gbWlzdGFrZSBpcyB0byB3cml0ZSBvbmVPZih4LCB5LCB6KSBpbnN0ZWFkIG9mIG9uZU9mKFt4LCB5LCB6XSkuJ1xuICAgICAgICAgICk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgcHJpbnRXYXJuaW5nKCdJbnZhbGlkIGFyZ3VtZW50IHN1cHBsaWVkIHRvIG9uZU9mLCBleHBlY3RlZCBhbiBhcnJheS4nKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgcmV0dXJuIGVtcHR5RnVuY3Rpb25UaGF0UmV0dXJuc051bGw7XG4gICAgfVxuXG4gICAgZnVuY3Rpb24gdmFsaWRhdGUocHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lKSB7XG4gICAgICB2YXIgcHJvcFZhbHVlID0gcHJvcHNbcHJvcE5hbWVdO1xuICAgICAgZm9yICh2YXIgaSA9IDA7IGkgPCBleHBlY3RlZFZhbHVlcy5sZW5ndGg7IGkrKykge1xuICAgICAgICBpZiAoaXMocHJvcFZhbHVlLCBleHBlY3RlZFZhbHVlc1tpXSkpIHtcbiAgICAgICAgICByZXR1cm4gbnVsbDtcbiAgICAgICAgfVxuICAgICAgfVxuXG4gICAgICB2YXIgdmFsdWVzU3RyaW5nID0gSlNPTi5zdHJpbmdpZnkoZXhwZWN0ZWRWYWx1ZXMsIGZ1bmN0aW9uIHJlcGxhY2VyKGtleSwgdmFsdWUpIHtcbiAgICAgICAgdmFyIHR5cGUgPSBnZXRQcmVjaXNlVHlwZSh2YWx1ZSk7XG4gICAgICAgIGlmICh0eXBlID09PSAnc3ltYm9sJykge1xuICAgICAgICAgIHJldHVybiBTdHJpbmcodmFsdWUpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiB2YWx1ZTtcbiAgICAgIH0pO1xuICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiB2YWx1ZSBgJyArIFN0cmluZyhwcm9wVmFsdWUpICsgJ2AgJyArICgnc3VwcGxpZWQgdG8gYCcgKyBjb21wb25lbnROYW1lICsgJ2AsIGV4cGVjdGVkIG9uZSBvZiAnICsgdmFsdWVzU3RyaW5nICsgJy4nKSk7XG4gICAgfVxuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSk7XG4gIH1cblxuICBmdW5jdGlvbiBjcmVhdGVPYmplY3RPZlR5cGVDaGVja2VyKHR5cGVDaGVja2VyKSB7XG4gICAgZnVuY3Rpb24gdmFsaWRhdGUocHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lKSB7XG4gICAgICBpZiAodHlwZW9mIHR5cGVDaGVja2VyICE9PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgIHJldHVybiBuZXcgUHJvcFR5cGVFcnJvcignUHJvcGVydHkgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiBjb21wb25lbnQgYCcgKyBjb21wb25lbnROYW1lICsgJ2AgaGFzIGludmFsaWQgUHJvcFR5cGUgbm90YXRpb24gaW5zaWRlIG9iamVjdE9mLicpO1xuICAgICAgfVxuICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICAgIHZhciBwcm9wVHlwZSA9IGdldFByb3BUeXBlKHByb3BWYWx1ZSk7XG4gICAgICBpZiAocHJvcFR5cGUgIT09ICdvYmplY3QnKSB7XG4gICAgICAgIHJldHVybiBuZXcgUHJvcFR5cGVFcnJvcignSW52YWxpZCAnICsgbG9jYXRpb24gKyAnIGAnICsgcHJvcEZ1bGxOYW1lICsgJ2Agb2YgdHlwZSAnICsgKCdgJyArIHByb3BUeXBlICsgJ2Agc3VwcGxpZWQgdG8gYCcgKyBjb21wb25lbnROYW1lICsgJ2AsIGV4cGVjdGVkIGFuIG9iamVjdC4nKSk7XG4gICAgICB9XG4gICAgICBmb3IgKHZhciBrZXkgaW4gcHJvcFZhbHVlKSB7XG4gICAgICAgIGlmIChoYXMocHJvcFZhbHVlLCBrZXkpKSB7XG4gICAgICAgICAgdmFyIGVycm9yID0gdHlwZUNoZWNrZXIocHJvcFZhbHVlLCBrZXksIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUgKyAnLicgKyBrZXksIFJlYWN0UHJvcFR5cGVzU2VjcmV0KTtcbiAgICAgICAgICBpZiAoZXJyb3IgaW5zdGFuY2VvZiBFcnJvcikge1xuICAgICAgICAgICAgcmV0dXJuIGVycm9yO1xuICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSk7XG4gIH1cblxuICBmdW5jdGlvbiBjcmVhdGVVbmlvblR5cGVDaGVja2VyKGFycmF5T2ZUeXBlQ2hlY2tlcnMpIHtcbiAgICBpZiAoIUFycmF5LmlzQXJyYXkoYXJyYXlPZlR5cGVDaGVja2VycykpIHtcbiAgICAgIHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicgPyBwcmludFdhcm5pbmcoJ0ludmFsaWQgYXJndW1lbnQgc3VwcGxpZWQgdG8gb25lT2ZUeXBlLCBleHBlY3RlZCBhbiBpbnN0YW5jZSBvZiBhcnJheS4nKSA6IHZvaWQgMDtcbiAgICAgIHJldHVybiBlbXB0eUZ1bmN0aW9uVGhhdFJldHVybnNOdWxsO1xuICAgIH1cblxuICAgIGZvciAodmFyIGkgPSAwOyBpIDwgYXJyYXlPZlR5cGVDaGVja2Vycy5sZW5ndGg7IGkrKykge1xuICAgICAgdmFyIGNoZWNrZXIgPSBhcnJheU9mVHlwZUNoZWNrZXJzW2ldO1xuICAgICAgaWYgKHR5cGVvZiBjaGVja2VyICE9PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgIHByaW50V2FybmluZyhcbiAgICAgICAgICAnSW52YWxpZCBhcmd1bWVudCBzdXBwbGllZCB0byBvbmVPZlR5cGUuIEV4cGVjdGVkIGFuIGFycmF5IG9mIGNoZWNrIGZ1bmN0aW9ucywgYnV0ICcgK1xuICAgICAgICAgICdyZWNlaXZlZCAnICsgZ2V0UG9zdGZpeEZvclR5cGVXYXJuaW5nKGNoZWNrZXIpICsgJyBhdCBpbmRleCAnICsgaSArICcuJ1xuICAgICAgICApO1xuICAgICAgICByZXR1cm4gZW1wdHlGdW5jdGlvblRoYXRSZXR1cm5zTnVsbDtcbiAgICAgIH1cbiAgICB9XG5cbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpIHtcbiAgICAgIHZhciBleHBlY3RlZFR5cGVzID0gW107XG4gICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGFycmF5T2ZUeXBlQ2hlY2tlcnMubGVuZ3RoOyBpKyspIHtcbiAgICAgICAgdmFyIGNoZWNrZXIgPSBhcnJheU9mVHlwZUNoZWNrZXJzW2ldO1xuICAgICAgICB2YXIgY2hlY2tlclJlc3VsdCA9IGNoZWNrZXIocHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lLCBSZWFjdFByb3BUeXBlc1NlY3JldCk7XG4gICAgICAgIGlmIChjaGVja2VyUmVzdWx0ID09IG51bGwpIHtcbiAgICAgICAgICByZXR1cm4gbnVsbDtcbiAgICAgICAgfVxuICAgICAgICBpZiAoY2hlY2tlclJlc3VsdC5kYXRhICYmIGhhcyhjaGVja2VyUmVzdWx0LmRhdGEsICdleHBlY3RlZFR5cGUnKSkge1xuICAgICAgICAgIGV4cGVjdGVkVHlwZXMucHVzaChjaGVja2VyUmVzdWx0LmRhdGEuZXhwZWN0ZWRUeXBlKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgdmFyIGV4cGVjdGVkVHlwZXNNZXNzYWdlID0gKGV4cGVjdGVkVHlwZXMubGVuZ3RoID4gMCkgPyAnLCBleHBlY3RlZCBvbmUgb2YgdHlwZSBbJyArIGV4cGVjdGVkVHlwZXMuam9pbignLCAnKSArICddJzogJyc7XG4gICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIHN1cHBsaWVkIHRvICcgKyAoJ2AnICsgY29tcG9uZW50TmFtZSArICdgJyArIGV4cGVjdGVkVHlwZXNNZXNzYWdlICsgJy4nKSk7XG4gICAgfVxuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSk7XG4gIH1cblxuICBmdW5jdGlvbiBjcmVhdGVOb2RlQ2hlY2tlcigpIHtcbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpIHtcbiAgICAgIGlmICghaXNOb2RlKHByb3BzW3Byb3BOYW1lXSkpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBzdXBwbGllZCB0byAnICsgKCdgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgYSBSZWFjdE5vZGUuJykpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSk7XG4gIH1cblxuICBmdW5jdGlvbiBpbnZhbGlkVmFsaWRhdG9yRXJyb3IoY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSwga2V5LCB0eXBlKSB7XG4gICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKFxuICAgICAgKGNvbXBvbmVudE5hbWUgfHwgJ1JlYWN0IGNsYXNzJykgKyAnOiAnICsgbG9jYXRpb24gKyAnIHR5cGUgYCcgKyBwcm9wRnVsbE5hbWUgKyAnLicgKyBrZXkgKyAnYCBpcyBpbnZhbGlkOyAnICtcbiAgICAgICdpdCBtdXN0IGJlIGEgZnVuY3Rpb24sIHVzdWFsbHkgZnJvbSB0aGUgYHByb3AtdHlwZXNgIHBhY2thZ2UsIGJ1dCByZWNlaXZlZCBgJyArIHR5cGUgKyAnYC4nXG4gICAgKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZVNoYXBlVHlwZUNoZWNrZXIoc2hhcGVUeXBlcykge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICAgIHZhciBwcm9wVHlwZSA9IGdldFByb3BUeXBlKHByb3BWYWx1ZSk7XG4gICAgICBpZiAocHJvcFR5cGUgIT09ICdvYmplY3QnKSB7XG4gICAgICAgIHJldHVybiBuZXcgUHJvcFR5cGVFcnJvcignSW52YWxpZCAnICsgbG9jYXRpb24gKyAnIGAnICsgcHJvcEZ1bGxOYW1lICsgJ2Agb2YgdHlwZSBgJyArIHByb3BUeXBlICsgJ2AgJyArICgnc3VwcGxpZWQgdG8gYCcgKyBjb21wb25lbnROYW1lICsgJ2AsIGV4cGVjdGVkIGBvYmplY3RgLicpKTtcbiAgICAgIH1cbiAgICAgIGZvciAodmFyIGtleSBpbiBzaGFwZVR5cGVzKSB7XG4gICAgICAgIHZhciBjaGVja2VyID0gc2hhcGVUeXBlc1trZXldO1xuICAgICAgICBpZiAodHlwZW9mIGNoZWNrZXIgIT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgICByZXR1cm4gaW52YWxpZFZhbGlkYXRvckVycm9yKGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUsIGtleSwgZ2V0UHJlY2lzZVR5cGUoY2hlY2tlcikpO1xuICAgICAgICB9XG4gICAgICAgIHZhciBlcnJvciA9IGNoZWNrZXIocHJvcFZhbHVlLCBrZXksIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUgKyAnLicgKyBrZXksIFJlYWN0UHJvcFR5cGVzU2VjcmV0KTtcbiAgICAgICAgaWYgKGVycm9yKSB7XG4gICAgICAgICAgcmV0dXJuIGVycm9yO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZVN0cmljdFNoYXBlVHlwZUNoZWNrZXIoc2hhcGVUeXBlcykge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICAgIHZhciBwcm9wVHlwZSA9IGdldFByb3BUeXBlKHByb3BWYWx1ZSk7XG4gICAgICBpZiAocHJvcFR5cGUgIT09ICdvYmplY3QnKSB7XG4gICAgICAgIHJldHVybiBuZXcgUHJvcFR5cGVFcnJvcignSW52YWxpZCAnICsgbG9jYXRpb24gKyAnIGAnICsgcHJvcEZ1bGxOYW1lICsgJ2Agb2YgdHlwZSBgJyArIHByb3BUeXBlICsgJ2AgJyArICgnc3VwcGxpZWQgdG8gYCcgKyBjb21wb25lbnROYW1lICsgJ2AsIGV4cGVjdGVkIGBvYmplY3RgLicpKTtcbiAgICAgIH1cbiAgICAgIC8vIFdlIG5lZWQgdG8gY2hlY2sgYWxsIGtleXMgaW4gY2FzZSBzb21lIGFyZSByZXF1aXJlZCBidXQgbWlzc2luZyBmcm9tIHByb3BzLlxuICAgICAgdmFyIGFsbEtleXMgPSBhc3NpZ24oe30sIHByb3BzW3Byb3BOYW1lXSwgc2hhcGVUeXBlcyk7XG4gICAgICBmb3IgKHZhciBrZXkgaW4gYWxsS2V5cykge1xuICAgICAgICB2YXIgY2hlY2tlciA9IHNoYXBlVHlwZXNba2V5XTtcbiAgICAgICAgaWYgKGhhcyhzaGFwZVR5cGVzLCBrZXkpICYmIHR5cGVvZiBjaGVja2VyICE9PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgICAgcmV0dXJuIGludmFsaWRWYWxpZGF0b3JFcnJvcihjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lLCBrZXksIGdldFByZWNpc2VUeXBlKGNoZWNrZXIpKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoIWNoZWNrZXIpIHtcbiAgICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoXG4gICAgICAgICAgICAnSW52YWxpZCAnICsgbG9jYXRpb24gKyAnIGAnICsgcHJvcEZ1bGxOYW1lICsgJ2Aga2V5IGAnICsga2V5ICsgJ2Agc3VwcGxpZWQgdG8gYCcgKyBjb21wb25lbnROYW1lICsgJ2AuJyArXG4gICAgICAgICAgICAnXFxuQmFkIG9iamVjdDogJyArIEpTT04uc3RyaW5naWZ5KHByb3BzW3Byb3BOYW1lXSwgbnVsbCwgJyAgJykgK1xuICAgICAgICAgICAgJ1xcblZhbGlkIGtleXM6ICcgKyBKU09OLnN0cmluZ2lmeShPYmplY3Qua2V5cyhzaGFwZVR5cGVzKSwgbnVsbCwgJyAgJylcbiAgICAgICAgICApO1xuICAgICAgICB9XG4gICAgICAgIHZhciBlcnJvciA9IGNoZWNrZXIocHJvcFZhbHVlLCBrZXksIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUgKyAnLicgKyBrZXksIFJlYWN0UHJvcFR5cGVzU2VjcmV0KTtcbiAgICAgICAgaWYgKGVycm9yKSB7XG4gICAgICAgICAgcmV0dXJuIGVycm9yO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG5cbiAgICByZXR1cm4gY3JlYXRlQ2hhaW5hYmxlVHlwZUNoZWNrZXIodmFsaWRhdGUpO1xuICB9XG5cbiAgZnVuY3Rpb24gaXNOb2RlKHByb3BWYWx1ZSkge1xuICAgIHN3aXRjaCAodHlwZW9mIHByb3BWYWx1ZSkge1xuICAgICAgY2FzZSAnbnVtYmVyJzpcbiAgICAgIGNhc2UgJ3N0cmluZyc6XG4gICAgICBjYXNlICd1bmRlZmluZWQnOlxuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgIGNhc2UgJ2Jvb2xlYW4nOlxuICAgICAgICByZXR1cm4gIXByb3BWYWx1ZTtcbiAgICAgIGNhc2UgJ29iamVjdCc6XG4gICAgICAgIGlmIChBcnJheS5pc0FycmF5KHByb3BWYWx1ZSkpIHtcbiAgICAgICAgICByZXR1cm4gcHJvcFZhbHVlLmV2ZXJ5KGlzTm9kZSk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHByb3BWYWx1ZSA9PT0gbnVsbCB8fCBpc1ZhbGlkRWxlbWVudChwcm9wVmFsdWUpKSB7XG4gICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgIH1cblxuICAgICAgICB2YXIgaXRlcmF0b3JGbiA9IGdldEl0ZXJhdG9yRm4ocHJvcFZhbHVlKTtcbiAgICAgICAgaWYgKGl0ZXJhdG9yRm4pIHtcbiAgICAgICAgICB2YXIgaXRlcmF0b3IgPSBpdGVyYXRvckZuLmNhbGwocHJvcFZhbHVlKTtcbiAgICAgICAgICB2YXIgc3RlcDtcbiAgICAgICAgICBpZiAoaXRlcmF0b3JGbiAhPT0gcHJvcFZhbHVlLmVudHJpZXMpIHtcbiAgICAgICAgICAgIHdoaWxlICghKHN0ZXAgPSBpdGVyYXRvci5uZXh0KCkpLmRvbmUpIHtcbiAgICAgICAgICAgICAgaWYgKCFpc05vZGUoc3RlcC52YWx1ZSkpIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgLy8gSXRlcmF0b3Igd2lsbCBwcm92aWRlIGVudHJ5IFtrLHZdIHR1cGxlcyByYXRoZXIgdGhhbiB2YWx1ZXMuXG4gICAgICAgICAgICB3aGlsZSAoIShzdGVwID0gaXRlcmF0b3IubmV4dCgpKS5kb25lKSB7XG4gICAgICAgICAgICAgIHZhciBlbnRyeSA9IHN0ZXAudmFsdWU7XG4gICAgICAgICAgICAgIGlmIChlbnRyeSkge1xuICAgICAgICAgICAgICAgIGlmICghaXNOb2RlKGVudHJ5WzFdKSkge1xuICAgICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgIH1cbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgIH1cblxuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgIGRlZmF1bHQ6XG4gICAgICAgIHJldHVybiBmYWxzZTtcbiAgICB9XG4gIH1cblxuICBmdW5jdGlvbiBpc1N5bWJvbChwcm9wVHlwZSwgcHJvcFZhbHVlKSB7XG4gICAgLy8gTmF0aXZlIFN5bWJvbC5cbiAgICBpZiAocHJvcFR5cGUgPT09ICdzeW1ib2wnKSB7XG4gICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG5cbiAgICAvLyBmYWxzeSB2YWx1ZSBjYW4ndCBiZSBhIFN5bWJvbFxuICAgIGlmICghcHJvcFZhbHVlKSB7XG4gICAgICByZXR1cm4gZmFsc2U7XG4gICAgfVxuXG4gICAgLy8gMTkuNC4zLjUgU3ltYm9sLnByb3RvdHlwZVtAQHRvU3RyaW5nVGFnXSA9PT0gJ1N5bWJvbCdcbiAgICBpZiAocHJvcFZhbHVlWydAQHRvU3RyaW5nVGFnJ10gPT09ICdTeW1ib2wnKSB7XG4gICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG5cbiAgICAvLyBGYWxsYmFjayBmb3Igbm9uLXNwZWMgY29tcGxpYW50IFN5bWJvbHMgd2hpY2ggYXJlIHBvbHlmaWxsZWQuXG4gICAgaWYgKHR5cGVvZiBTeW1ib2wgPT09ICdmdW5jdGlvbicgJiYgcHJvcFZhbHVlIGluc3RhbmNlb2YgU3ltYm9sKSB7XG4gICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG5cbiAgICByZXR1cm4gZmFsc2U7XG4gIH1cblxuICAvLyBFcXVpdmFsZW50IG9mIGB0eXBlb2ZgIGJ1dCB3aXRoIHNwZWNpYWwgaGFuZGxpbmcgZm9yIGFycmF5IGFuZCByZWdleHAuXG4gIGZ1bmN0aW9uIGdldFByb3BUeXBlKHByb3BWYWx1ZSkge1xuICAgIHZhciBwcm9wVHlwZSA9IHR5cGVvZiBwcm9wVmFsdWU7XG4gICAgaWYgKEFycmF5LmlzQXJyYXkocHJvcFZhbHVlKSkge1xuICAgICAgcmV0dXJuICdhcnJheSc7XG4gICAgfVxuICAgIGlmIChwcm9wVmFsdWUgaW5zdGFuY2VvZiBSZWdFeHApIHtcbiAgICAgIC8vIE9sZCB3ZWJraXRzIChhdCBsZWFzdCB1bnRpbCBBbmRyb2lkIDQuMCkgcmV0dXJuICdmdW5jdGlvbicgcmF0aGVyIHRoYW5cbiAgICAgIC8vICdvYmplY3QnIGZvciB0eXBlb2YgYSBSZWdFeHAuIFdlJ2xsIG5vcm1hbGl6ZSB0aGlzIGhlcmUgc28gdGhhdCAvYmxhL1xuICAgICAgLy8gcGFzc2VzIFByb3BUeXBlcy5vYmplY3QuXG4gICAgICByZXR1cm4gJ29iamVjdCc7XG4gICAgfVxuICAgIGlmIChpc1N5bWJvbChwcm9wVHlwZSwgcHJvcFZhbHVlKSkge1xuICAgICAgcmV0dXJuICdzeW1ib2wnO1xuICAgIH1cbiAgICByZXR1cm4gcHJvcFR5cGU7XG4gIH1cblxuICAvLyBUaGlzIGhhbmRsZXMgbW9yZSB0eXBlcyB0aGFuIGBnZXRQcm9wVHlwZWAuIE9ubHkgdXNlZCBmb3IgZXJyb3IgbWVzc2FnZXMuXG4gIC8vIFNlZSBgY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXJgLlxuICBmdW5jdGlvbiBnZXRQcmVjaXNlVHlwZShwcm9wVmFsdWUpIHtcbiAgICBpZiAodHlwZW9mIHByb3BWYWx1ZSA9PT0gJ3VuZGVmaW5lZCcgfHwgcHJvcFZhbHVlID09PSBudWxsKSB7XG4gICAgICByZXR1cm4gJycgKyBwcm9wVmFsdWU7XG4gICAgfVxuICAgIHZhciBwcm9wVHlwZSA9IGdldFByb3BUeXBlKHByb3BWYWx1ZSk7XG4gICAgaWYgKHByb3BUeXBlID09PSAnb2JqZWN0Jykge1xuICAgICAgaWYgKHByb3BWYWx1ZSBpbnN0YW5jZW9mIERhdGUpIHtcbiAgICAgICAgcmV0dXJuICdkYXRlJztcbiAgICAgIH0gZWxzZSBpZiAocHJvcFZhbHVlIGluc3RhbmNlb2YgUmVnRXhwKSB7XG4gICAgICAgIHJldHVybiAncmVnZXhwJztcbiAgICAgIH1cbiAgICB9XG4gICAgcmV0dXJuIHByb3BUeXBlO1xuICB9XG5cbiAgLy8gUmV0dXJucyBhIHN0cmluZyB0aGF0IGlzIHBvc3RmaXhlZCB0byBhIHdhcm5pbmcgYWJvdXQgYW4gaW52YWxpZCB0eXBlLlxuICAvLyBGb3IgZXhhbXBsZSwgXCJ1bmRlZmluZWRcIiBvciBcIm9mIHR5cGUgYXJyYXlcIlxuICBmdW5jdGlvbiBnZXRQb3N0Zml4Rm9yVHlwZVdhcm5pbmcodmFsdWUpIHtcbiAgICB2YXIgdHlwZSA9IGdldFByZWNpc2VUeXBlKHZhbHVlKTtcbiAgICBzd2l0Y2ggKHR5cGUpIHtcbiAgICAgIGNhc2UgJ2FycmF5JzpcbiAgICAgIGNhc2UgJ29iamVjdCc6XG4gICAgICAgIHJldHVybiAnYW4gJyArIHR5cGU7XG4gICAgICBjYXNlICdib29sZWFuJzpcbiAgICAgIGNhc2UgJ2RhdGUnOlxuICAgICAgY2FzZSAncmVnZXhwJzpcbiAgICAgICAgcmV0dXJuICdhICcgKyB0eXBlO1xuICAgICAgZGVmYXVsdDpcbiAgICAgICAgcmV0dXJuIHR5cGU7XG4gICAgfVxuICB9XG5cbiAgLy8gUmV0dXJucyBjbGFzcyBuYW1lIG9mIHRoZSBvYmplY3QsIGlmIGFueS5cbiAgZnVuY3Rpb24gZ2V0Q2xhc3NOYW1lKHByb3BWYWx1ZSkge1xuICAgIGlmICghcHJvcFZhbHVlLmNvbnN0cnVjdG9yIHx8ICFwcm9wVmFsdWUuY29uc3RydWN0b3IubmFtZSkge1xuICAgICAgcmV0dXJuIEFOT05ZTU9VUztcbiAgICB9XG4gICAgcmV0dXJuIHByb3BWYWx1ZS5jb25zdHJ1Y3Rvci5uYW1lO1xuICB9XG5cbiAgUmVhY3RQcm9wVHlwZXMuY2hlY2tQcm9wVHlwZXMgPSBjaGVja1Byb3BUeXBlcztcbiAgUmVhY3RQcm9wVHlwZXMucmVzZXRXYXJuaW5nQ2FjaGUgPSBjaGVja1Byb3BUeXBlcy5yZXNldFdhcm5pbmdDYWNoZTtcbiAgUmVhY3RQcm9wVHlwZXMuUHJvcFR5cGVzID0gUmVhY3RQcm9wVHlwZXM7XG5cbiAgcmV0dXJuIFJlYWN0UHJvcFR5cGVzO1xufTtcbiIsIi8qKlxuICogQ29weXJpZ2h0IChjKSAyMDEzLXByZXNlbnQsIEZhY2Vib29rLCBJbmMuXG4gKlxuICogVGhpcyBzb3VyY2UgY29kZSBpcyBsaWNlbnNlZCB1bmRlciB0aGUgTUlUIGxpY2Vuc2UgZm91bmQgaW4gdGhlXG4gKiBMSUNFTlNFIGZpbGUgaW4gdGhlIHJvb3QgZGlyZWN0b3J5IG9mIHRoaXMgc291cmNlIHRyZWUuXG4gKi9cblxuaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicpIHtcbiAgdmFyIFJlYWN0SXMgPSByZXF1aXJlKCdyZWFjdC1pcycpO1xuXG4gIC8vIEJ5IGV4cGxpY2l0bHkgdXNpbmcgYHByb3AtdHlwZXNgIHlvdSBhcmUgb3B0aW5nIGludG8gbmV3IGRldmVsb3BtZW50IGJlaGF2aW9yLlxuICAvLyBodHRwOi8vZmIubWUvcHJvcC10eXBlcy1pbi1wcm9kXG4gIHZhciB0aHJvd09uRGlyZWN0QWNjZXNzID0gdHJ1ZTtcbiAgbW9kdWxlLmV4cG9ydHMgPSByZXF1aXJlKCcuL2ZhY3RvcnlXaXRoVHlwZUNoZWNrZXJzJykoUmVhY3RJcy5pc0VsZW1lbnQsIHRocm93T25EaXJlY3RBY2Nlc3MpO1xufSBlbHNlIHtcbiAgLy8gQnkgZXhwbGljaXRseSB1c2luZyBgcHJvcC10eXBlc2AgeW91IGFyZSBvcHRpbmcgaW50byBuZXcgcHJvZHVjdGlvbiBiZWhhdmlvci5cbiAgLy8gaHR0cDovL2ZiLm1lL3Byb3AtdHlwZXMtaW4tcHJvZFxuICBtb2R1bGUuZXhwb3J0cyA9IHJlcXVpcmUoJy4vZmFjdG9yeVdpdGhUaHJvd2luZ1NoaW1zJykoKTtcbn1cbiIsImV4cG9ydCBkZWZhdWx0IHtcbiAgZGlzYWJsZWQ6IGZhbHNlXG59OyIsImltcG9ydCBQcm9wVHlwZXMgZnJvbSAncHJvcC10eXBlcyc7XG5leHBvcnQgdmFyIHRpbWVvdXRzU2hhcGUgPSBwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gJ3Byb2R1Y3Rpb24nID8gUHJvcFR5cGVzLm9uZU9mVHlwZShbUHJvcFR5cGVzLm51bWJlciwgUHJvcFR5cGVzLnNoYXBlKHtcbiAgZW50ZXI6IFByb3BUeXBlcy5udW1iZXIsXG4gIGV4aXQ6IFByb3BUeXBlcy5udW1iZXIsXG4gIGFwcGVhcjogUHJvcFR5cGVzLm51bWJlclxufSkuaXNSZXF1aXJlZF0pIDogbnVsbDtcbmV4cG9ydCB2YXIgY2xhc3NOYW1lc1NoYXBlID0gcHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09ICdwcm9kdWN0aW9uJyA/IFByb3BUeXBlcy5vbmVPZlR5cGUoW1Byb3BUeXBlcy5zdHJpbmcsIFByb3BUeXBlcy5zaGFwZSh7XG4gIGVudGVyOiBQcm9wVHlwZXMuc3RyaW5nLFxuICBleGl0OiBQcm9wVHlwZXMuc3RyaW5nLFxuICBhY3RpdmU6IFByb3BUeXBlcy5zdHJpbmdcbn0pLCBQcm9wVHlwZXMuc2hhcGUoe1xuICBlbnRlcjogUHJvcFR5cGVzLnN0cmluZyxcbiAgZW50ZXJEb25lOiBQcm9wVHlwZXMuc3RyaW5nLFxuICBlbnRlckFjdGl2ZTogUHJvcFR5cGVzLnN0cmluZyxcbiAgZXhpdDogUHJvcFR5cGVzLnN0cmluZyxcbiAgZXhpdERvbmU6IFByb3BUeXBlcy5zdHJpbmcsXG4gIGV4aXRBY3RpdmU6IFByb3BUeXBlcy5zdHJpbmdcbn0pXSkgOiBudWxsOyIsImltcG9ydCBSZWFjdCBmcm9tICdyZWFjdCc7XG5leHBvcnQgZGVmYXVsdCBSZWFjdC5jcmVhdGVDb250ZXh0KG51bGwpOyIsImV4cG9ydCB2YXIgZm9yY2VSZWZsb3cgPSBmdW5jdGlvbiBmb3JjZVJlZmxvdyhub2RlKSB7XG4gIHJldHVybiBub2RlLnNjcm9sbFRvcDtcbn07IiwiaW1wb3J0IF9vYmplY3RXaXRob3V0UHJvcGVydGllc0xvb3NlIGZyb20gXCJAYmFiZWwvcnVudGltZS9oZWxwZXJzL2VzbS9vYmplY3RXaXRob3V0UHJvcGVydGllc0xvb3NlXCI7XG5pbXBvcnQgX2luaGVyaXRzTG9vc2UgZnJvbSBcIkBiYWJlbC9ydW50aW1lL2hlbHBlcnMvZXNtL2luaGVyaXRzTG9vc2VcIjtcbmltcG9ydCBQcm9wVHlwZXMgZnJvbSAncHJvcC10eXBlcyc7XG5pbXBvcnQgUmVhY3QgZnJvbSAncmVhY3QnO1xuaW1wb3J0IFJlYWN0RE9NIGZyb20gJ3JlYWN0LWRvbSc7XG5pbXBvcnQgY29uZmlnIGZyb20gJy4vY29uZmlnJztcbmltcG9ydCB7IHRpbWVvdXRzU2hhcGUgfSBmcm9tICcuL3V0aWxzL1Byb3BUeXBlcyc7XG5pbXBvcnQgVHJhbnNpdGlvbkdyb3VwQ29udGV4dCBmcm9tICcuL1RyYW5zaXRpb25Hcm91cENvbnRleHQnO1xuaW1wb3J0IHsgZm9yY2VSZWZsb3cgfSBmcm9tICcuL3V0aWxzL3JlZmxvdyc7XG5leHBvcnQgdmFyIFVOTU9VTlRFRCA9ICd1bm1vdW50ZWQnO1xuZXhwb3J0IHZhciBFWElURUQgPSAnZXhpdGVkJztcbmV4cG9ydCB2YXIgRU5URVJJTkcgPSAnZW50ZXJpbmcnO1xuZXhwb3J0IHZhciBFTlRFUkVEID0gJ2VudGVyZWQnO1xuZXhwb3J0IHZhciBFWElUSU5HID0gJ2V4aXRpbmcnO1xuLyoqXG4gKiBUaGUgVHJhbnNpdGlvbiBjb21wb25lbnQgbGV0cyB5b3UgZGVzY3JpYmUgYSB0cmFuc2l0aW9uIGZyb20gb25lIGNvbXBvbmVudFxuICogc3RhdGUgdG8gYW5vdGhlciBfb3ZlciB0aW1lXyB3aXRoIGEgc2ltcGxlIGRlY2xhcmF0aXZlIEFQSS4gTW9zdCBjb21tb25seVxuICogaXQncyB1c2VkIHRvIGFuaW1hdGUgdGhlIG1vdW50aW5nIGFuZCB1bm1vdW50aW5nIG9mIGEgY29tcG9uZW50LCBidXQgY2FuIGFsc29cbiAqIGJlIHVzZWQgdG8gZGVzY3JpYmUgaW4tcGxhY2UgdHJhbnNpdGlvbiBzdGF0ZXMgYXMgd2VsbC5cbiAqXG4gKiAtLS1cbiAqXG4gKiAqKk5vdGUqKjogYFRyYW5zaXRpb25gIGlzIGEgcGxhdGZvcm0tYWdub3N0aWMgYmFzZSBjb21wb25lbnQuIElmIHlvdSdyZSB1c2luZ1xuICogdHJhbnNpdGlvbnMgaW4gQ1NTLCB5b3UnbGwgcHJvYmFibHkgd2FudCB0byB1c2VcbiAqIFtgQ1NTVHJhbnNpdGlvbmBdKGh0dHBzOi8vcmVhY3Rjb21tdW5pdHkub3JnL3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvY3NzLXRyYW5zaXRpb24pXG4gKiBpbnN0ZWFkLiBJdCBpbmhlcml0cyBhbGwgdGhlIGZlYXR1cmVzIG9mIGBUcmFuc2l0aW9uYCwgYnV0IGNvbnRhaW5zXG4gKiBhZGRpdGlvbmFsIGZlYXR1cmVzIG5lY2Vzc2FyeSB0byBwbGF5IG5pY2Ugd2l0aCBDU1MgdHJhbnNpdGlvbnMgKGhlbmNlIHRoZVxuICogbmFtZSBvZiB0aGUgY29tcG9uZW50KS5cbiAqXG4gKiAtLS1cbiAqXG4gKiBCeSBkZWZhdWx0IHRoZSBgVHJhbnNpdGlvbmAgY29tcG9uZW50IGRvZXMgbm90IGFsdGVyIHRoZSBiZWhhdmlvciBvZiB0aGVcbiAqIGNvbXBvbmVudCBpdCByZW5kZXJzLCBpdCBvbmx5IHRyYWNrcyBcImVudGVyXCIgYW5kIFwiZXhpdFwiIHN0YXRlcyBmb3IgdGhlXG4gKiBjb21wb25lbnRzLiBJdCdzIHVwIHRvIHlvdSB0byBnaXZlIG1lYW5pbmcgYW5kIGVmZmVjdCB0byB0aG9zZSBzdGF0ZXMuIEZvclxuICogZXhhbXBsZSB3ZSBjYW4gYWRkIHN0eWxlcyB0byBhIGNvbXBvbmVudCB3aGVuIGl0IGVudGVycyBvciBleGl0czpcbiAqXG4gKiBgYGBqc3hcbiAqIGltcG9ydCB7IFRyYW5zaXRpb24gfSBmcm9tICdyZWFjdC10cmFuc2l0aW9uLWdyb3VwJztcbiAqXG4gKiBjb25zdCBkdXJhdGlvbiA9IDMwMDtcbiAqXG4gKiBjb25zdCBkZWZhdWx0U3R5bGUgPSB7XG4gKiAgIHRyYW5zaXRpb246IGBvcGFjaXR5ICR7ZHVyYXRpb259bXMgZWFzZS1pbi1vdXRgLFxuICogICBvcGFjaXR5OiAwLFxuICogfVxuICpcbiAqIGNvbnN0IHRyYW5zaXRpb25TdHlsZXMgPSB7XG4gKiAgIGVudGVyaW5nOiB7IG9wYWNpdHk6IDEgfSxcbiAqICAgZW50ZXJlZDogIHsgb3BhY2l0eTogMSB9LFxuICogICBleGl0aW5nOiAgeyBvcGFjaXR5OiAwIH0sXG4gKiAgIGV4aXRlZDogIHsgb3BhY2l0eTogMCB9LFxuICogfTtcbiAqXG4gKiBjb25zdCBGYWRlID0gKHsgaW46IGluUHJvcCB9KSA9PiAoXG4gKiAgIDxUcmFuc2l0aW9uIGluPXtpblByb3B9IHRpbWVvdXQ9e2R1cmF0aW9ufT5cbiAqICAgICB7c3RhdGUgPT4gKFxuICogICAgICAgPGRpdiBzdHlsZT17e1xuICogICAgICAgICAuLi5kZWZhdWx0U3R5bGUsXG4gKiAgICAgICAgIC4uLnRyYW5zaXRpb25TdHlsZXNbc3RhdGVdXG4gKiAgICAgICB9fT5cbiAqICAgICAgICAgSSdtIGEgZmFkZSBUcmFuc2l0aW9uIVxuICogICAgICAgPC9kaXY+XG4gKiAgICAgKX1cbiAqICAgPC9UcmFuc2l0aW9uPlxuICogKTtcbiAqIGBgYFxuICpcbiAqIFRoZXJlIGFyZSA0IG1haW4gc3RhdGVzIGEgVHJhbnNpdGlvbiBjYW4gYmUgaW46XG4gKiAgLSBgJ2VudGVyaW5nJ2BcbiAqICAtIGAnZW50ZXJlZCdgXG4gKiAgLSBgJ2V4aXRpbmcnYFxuICogIC0gYCdleGl0ZWQnYFxuICpcbiAqIFRyYW5zaXRpb24gc3RhdGUgaXMgdG9nZ2xlZCB2aWEgdGhlIGBpbmAgcHJvcC4gV2hlbiBgdHJ1ZWAgdGhlIGNvbXBvbmVudFxuICogYmVnaW5zIHRoZSBcIkVudGVyXCIgc3RhZ2UuIER1cmluZyB0aGlzIHN0YWdlLCB0aGUgY29tcG9uZW50IHdpbGwgc2hpZnQgZnJvbVxuICogaXRzIGN1cnJlbnQgdHJhbnNpdGlvbiBzdGF0ZSwgdG8gYCdlbnRlcmluZydgIGZvciB0aGUgZHVyYXRpb24gb2YgdGhlXG4gKiB0cmFuc2l0aW9uIGFuZCB0aGVuIHRvIHRoZSBgJ2VudGVyZWQnYCBzdGFnZSBvbmNlIGl0J3MgY29tcGxldGUuIExldCdzIHRha2VcbiAqIHRoZSBmb2xsb3dpbmcgZXhhbXBsZSAod2UnbGwgdXNlIHRoZVxuICogW3VzZVN0YXRlXShodHRwczovL3JlYWN0anMub3JnL2RvY3MvaG9va3MtcmVmZXJlbmNlLmh0bWwjdXNlc3RhdGUpIGhvb2spOlxuICpcbiAqIGBgYGpzeFxuICogZnVuY3Rpb24gQXBwKCkge1xuICogICBjb25zdCBbaW5Qcm9wLCBzZXRJblByb3BdID0gdXNlU3RhdGUoZmFsc2UpO1xuICogICByZXR1cm4gKFxuICogICAgIDxkaXY+XG4gKiAgICAgICA8VHJhbnNpdGlvbiBpbj17aW5Qcm9wfSB0aW1lb3V0PXs1MDB9PlxuICogICAgICAgICB7c3RhdGUgPT4gKFxuICogICAgICAgICAgIC8vIC4uLlxuICogICAgICAgICApfVxuICogICAgICAgPC9UcmFuc2l0aW9uPlxuICogICAgICAgPGJ1dHRvbiBvbkNsaWNrPXsoKSA9PiBzZXRJblByb3AodHJ1ZSl9PlxuICogICAgICAgICBDbGljayB0byBFbnRlclxuICogICAgICAgPC9idXR0b24+XG4gKiAgICAgPC9kaXY+XG4gKiAgICk7XG4gKiB9XG4gKiBgYGBcbiAqXG4gKiBXaGVuIHRoZSBidXR0b24gaXMgY2xpY2tlZCB0aGUgY29tcG9uZW50IHdpbGwgc2hpZnQgdG8gdGhlIGAnZW50ZXJpbmcnYCBzdGF0ZVxuICogYW5kIHN0YXkgdGhlcmUgZm9yIDUwMG1zICh0aGUgdmFsdWUgb2YgYHRpbWVvdXRgKSBiZWZvcmUgaXQgZmluYWxseSBzd2l0Y2hlc1xuICogdG8gYCdlbnRlcmVkJ2AuXG4gKlxuICogV2hlbiBgaW5gIGlzIGBmYWxzZWAgdGhlIHNhbWUgdGhpbmcgaGFwcGVucyBleGNlcHQgdGhlIHN0YXRlIG1vdmVzIGZyb21cbiAqIGAnZXhpdGluZydgIHRvIGAnZXhpdGVkJ2AuXG4gKi9cblxudmFyIFRyYW5zaXRpb24gPSAvKiNfX1BVUkVfXyovZnVuY3Rpb24gKF9SZWFjdCRDb21wb25lbnQpIHtcbiAgX2luaGVyaXRzTG9vc2UoVHJhbnNpdGlvbiwgX1JlYWN0JENvbXBvbmVudCk7XG5cbiAgZnVuY3Rpb24gVHJhbnNpdGlvbihwcm9wcywgY29udGV4dCkge1xuICAgIHZhciBfdGhpcztcblxuICAgIF90aGlzID0gX1JlYWN0JENvbXBvbmVudC5jYWxsKHRoaXMsIHByb3BzLCBjb250ZXh0KSB8fCB0aGlzO1xuICAgIHZhciBwYXJlbnRHcm91cCA9IGNvbnRleHQ7IC8vIEluIHRoZSBjb250ZXh0IG9mIGEgVHJhbnNpdGlvbkdyb3VwIGFsbCBlbnRlcnMgYXJlIHJlYWxseSBhcHBlYXJzXG5cbiAgICB2YXIgYXBwZWFyID0gcGFyZW50R3JvdXAgJiYgIXBhcmVudEdyb3VwLmlzTW91bnRpbmcgPyBwcm9wcy5lbnRlciA6IHByb3BzLmFwcGVhcjtcbiAgICB2YXIgaW5pdGlhbFN0YXR1cztcbiAgICBfdGhpcy5hcHBlYXJTdGF0dXMgPSBudWxsO1xuXG4gICAgaWYgKHByb3BzLmluKSB7XG4gICAgICBpZiAoYXBwZWFyKSB7XG4gICAgICAgIGluaXRpYWxTdGF0dXMgPSBFWElURUQ7XG4gICAgICAgIF90aGlzLmFwcGVhclN0YXR1cyA9IEVOVEVSSU5HO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgaW5pdGlhbFN0YXR1cyA9IEVOVEVSRUQ7XG4gICAgICB9XG4gICAgfSBlbHNlIHtcbiAgICAgIGlmIChwcm9wcy51bm1vdW50T25FeGl0IHx8IHByb3BzLm1vdW50T25FbnRlcikge1xuICAgICAgICBpbml0aWFsU3RhdHVzID0gVU5NT1VOVEVEO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgaW5pdGlhbFN0YXR1cyA9IEVYSVRFRDtcbiAgICAgIH1cbiAgICB9XG5cbiAgICBfdGhpcy5zdGF0ZSA9IHtcbiAgICAgIHN0YXR1czogaW5pdGlhbFN0YXR1c1xuICAgIH07XG4gICAgX3RoaXMubmV4dENhbGxiYWNrID0gbnVsbDtcbiAgICByZXR1cm4gX3RoaXM7XG4gIH1cblxuICBUcmFuc2l0aW9uLmdldERlcml2ZWRTdGF0ZUZyb21Qcm9wcyA9IGZ1bmN0aW9uIGdldERlcml2ZWRTdGF0ZUZyb21Qcm9wcyhfcmVmLCBwcmV2U3RhdGUpIHtcbiAgICB2YXIgbmV4dEluID0gX3JlZi5pbjtcblxuICAgIGlmIChuZXh0SW4gJiYgcHJldlN0YXRlLnN0YXR1cyA9PT0gVU5NT1VOVEVEKSB7XG4gICAgICByZXR1cm4ge1xuICAgICAgICBzdGF0dXM6IEVYSVRFRFxuICAgICAgfTtcbiAgICB9XG5cbiAgICByZXR1cm4gbnVsbDtcbiAgfSAvLyBnZXRTbmFwc2hvdEJlZm9yZVVwZGF0ZShwcmV2UHJvcHMpIHtcbiAgLy8gICBsZXQgbmV4dFN0YXR1cyA9IG51bGxcbiAgLy8gICBpZiAocHJldlByb3BzICE9PSB0aGlzLnByb3BzKSB7XG4gIC8vICAgICBjb25zdCB7IHN0YXR1cyB9ID0gdGhpcy5zdGF0ZVxuICAvLyAgICAgaWYgKHRoaXMucHJvcHMuaW4pIHtcbiAgLy8gICAgICAgaWYgKHN0YXR1cyAhPT0gRU5URVJJTkcgJiYgc3RhdHVzICE9PSBFTlRFUkVEKSB7XG4gIC8vICAgICAgICAgbmV4dFN0YXR1cyA9IEVOVEVSSU5HXG4gIC8vICAgICAgIH1cbiAgLy8gICAgIH0gZWxzZSB7XG4gIC8vICAgICAgIGlmIChzdGF0dXMgPT09IEVOVEVSSU5HIHx8IHN0YXR1cyA9PT0gRU5URVJFRCkge1xuICAvLyAgICAgICAgIG5leHRTdGF0dXMgPSBFWElUSU5HXG4gIC8vICAgICAgIH1cbiAgLy8gICAgIH1cbiAgLy8gICB9XG4gIC8vICAgcmV0dXJuIHsgbmV4dFN0YXR1cyB9XG4gIC8vIH1cbiAgO1xuXG4gIHZhciBfcHJvdG8gPSBUcmFuc2l0aW9uLnByb3RvdHlwZTtcblxuICBfcHJvdG8uY29tcG9uZW50RGlkTW91bnQgPSBmdW5jdGlvbiBjb21wb25lbnREaWRNb3VudCgpIHtcbiAgICB0aGlzLnVwZGF0ZVN0YXR1cyh0cnVlLCB0aGlzLmFwcGVhclN0YXR1cyk7XG4gIH07XG5cbiAgX3Byb3RvLmNvbXBvbmVudERpZFVwZGF0ZSA9IGZ1bmN0aW9uIGNvbXBvbmVudERpZFVwZGF0ZShwcmV2UHJvcHMpIHtcbiAgICB2YXIgbmV4dFN0YXR1cyA9IG51bGw7XG5cbiAgICBpZiAocHJldlByb3BzICE9PSB0aGlzLnByb3BzKSB7XG4gICAgICB2YXIgc3RhdHVzID0gdGhpcy5zdGF0ZS5zdGF0dXM7XG5cbiAgICAgIGlmICh0aGlzLnByb3BzLmluKSB7XG4gICAgICAgIGlmIChzdGF0dXMgIT09IEVOVEVSSU5HICYmIHN0YXR1cyAhPT0gRU5URVJFRCkge1xuICAgICAgICAgIG5leHRTdGF0dXMgPSBFTlRFUklORztcbiAgICAgICAgfVxuICAgICAgfSBlbHNlIHtcbiAgICAgICAgaWYgKHN0YXR1cyA9PT0gRU5URVJJTkcgfHwgc3RhdHVzID09PSBFTlRFUkVEKSB7XG4gICAgICAgICAgbmV4dFN0YXR1cyA9IEVYSVRJTkc7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICB9XG5cbiAgICB0aGlzLnVwZGF0ZVN0YXR1cyhmYWxzZSwgbmV4dFN0YXR1cyk7XG4gIH07XG5cbiAgX3Byb3RvLmNvbXBvbmVudFdpbGxVbm1vdW50ID0gZnVuY3Rpb24gY29tcG9uZW50V2lsbFVubW91bnQoKSB7XG4gICAgdGhpcy5jYW5jZWxOZXh0Q2FsbGJhY2soKTtcbiAgfTtcblxuICBfcHJvdG8uZ2V0VGltZW91dHMgPSBmdW5jdGlvbiBnZXRUaW1lb3V0cygpIHtcbiAgICB2YXIgdGltZW91dCA9IHRoaXMucHJvcHMudGltZW91dDtcbiAgICB2YXIgZXhpdCwgZW50ZXIsIGFwcGVhcjtcbiAgICBleGl0ID0gZW50ZXIgPSBhcHBlYXIgPSB0aW1lb3V0O1xuXG4gICAgaWYgKHRpbWVvdXQgIT0gbnVsbCAmJiB0eXBlb2YgdGltZW91dCAhPT0gJ251bWJlcicpIHtcbiAgICAgIGV4aXQgPSB0aW1lb3V0LmV4aXQ7XG4gICAgICBlbnRlciA9IHRpbWVvdXQuZW50ZXI7IC8vIFRPRE86IHJlbW92ZSBmYWxsYmFjayBmb3IgbmV4dCBtYWpvclxuXG4gICAgICBhcHBlYXIgPSB0aW1lb3V0LmFwcGVhciAhPT0gdW5kZWZpbmVkID8gdGltZW91dC5hcHBlYXIgOiBlbnRlcjtcbiAgICB9XG5cbiAgICByZXR1cm4ge1xuICAgICAgZXhpdDogZXhpdCxcbiAgICAgIGVudGVyOiBlbnRlcixcbiAgICAgIGFwcGVhcjogYXBwZWFyXG4gICAgfTtcbiAgfTtcblxuICBfcHJvdG8udXBkYXRlU3RhdHVzID0gZnVuY3Rpb24gdXBkYXRlU3RhdHVzKG1vdW50aW5nLCBuZXh0U3RhdHVzKSB7XG4gICAgaWYgKG1vdW50aW5nID09PSB2b2lkIDApIHtcbiAgICAgIG1vdW50aW5nID0gZmFsc2U7XG4gICAgfVxuXG4gICAgaWYgKG5leHRTdGF0dXMgIT09IG51bGwpIHtcbiAgICAgIC8vIG5leHRTdGF0dXMgd2lsbCBhbHdheXMgYmUgRU5URVJJTkcgb3IgRVhJVElORy5cbiAgICAgIHRoaXMuY2FuY2VsTmV4dENhbGxiYWNrKCk7XG5cbiAgICAgIGlmIChuZXh0U3RhdHVzID09PSBFTlRFUklORykge1xuICAgICAgICBpZiAodGhpcy5wcm9wcy51bm1vdW50T25FeGl0IHx8IHRoaXMucHJvcHMubW91bnRPbkVudGVyKSB7XG4gICAgICAgICAgdmFyIG5vZGUgPSB0aGlzLnByb3BzLm5vZGVSZWYgPyB0aGlzLnByb3BzLm5vZGVSZWYuY3VycmVudCA6IFJlYWN0RE9NLmZpbmRET01Ob2RlKHRoaXMpOyAvLyBodHRwczovL2dpdGh1Yi5jb20vcmVhY3Rqcy9yZWFjdC10cmFuc2l0aW9uLWdyb3VwL3B1bGwvNzQ5XG4gICAgICAgICAgLy8gV2l0aCB1bm1vdW50T25FeGl0IG9yIG1vdW50T25FbnRlciwgdGhlIGVudGVyIGFuaW1hdGlvbiBzaG91bGQgaGFwcGVuIGF0IHRoZSB0cmFuc2l0aW9uIGJldHdlZW4gYGV4aXRlZGAgYW5kIGBlbnRlcmluZ2AuXG4gICAgICAgICAgLy8gVG8gbWFrZSB0aGUgYW5pbWF0aW9uIGhhcHBlbiwgIHdlIGhhdmUgdG8gc2VwYXJhdGUgZWFjaCByZW5kZXJpbmcgYW5kIGF2b2lkIGJlaW5nIHByb2Nlc3NlZCBhcyBiYXRjaGVkLlxuXG4gICAgICAgICAgaWYgKG5vZGUpIGZvcmNlUmVmbG93KG5vZGUpO1xuICAgICAgICB9XG5cbiAgICAgICAgdGhpcy5wZXJmb3JtRW50ZXIobW91bnRpbmcpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgdGhpcy5wZXJmb3JtRXhpdCgpO1xuICAgICAgfVxuICAgIH0gZWxzZSBpZiAodGhpcy5wcm9wcy51bm1vdW50T25FeGl0ICYmIHRoaXMuc3RhdGUuc3RhdHVzID09PSBFWElURUQpIHtcbiAgICAgIHRoaXMuc2V0U3RhdGUoe1xuICAgICAgICBzdGF0dXM6IFVOTU9VTlRFRFxuICAgICAgfSk7XG4gICAgfVxuICB9O1xuXG4gIF9wcm90by5wZXJmb3JtRW50ZXIgPSBmdW5jdGlvbiBwZXJmb3JtRW50ZXIobW91bnRpbmcpIHtcbiAgICB2YXIgX3RoaXMyID0gdGhpcztcblxuICAgIHZhciBlbnRlciA9IHRoaXMucHJvcHMuZW50ZXI7XG4gICAgdmFyIGFwcGVhcmluZyA9IHRoaXMuY29udGV4dCA/IHRoaXMuY29udGV4dC5pc01vdW50aW5nIDogbW91bnRpbmc7XG5cbiAgICB2YXIgX3JlZjIgPSB0aGlzLnByb3BzLm5vZGVSZWYgPyBbYXBwZWFyaW5nXSA6IFtSZWFjdERPTS5maW5kRE9NTm9kZSh0aGlzKSwgYXBwZWFyaW5nXSxcbiAgICAgICAgbWF5YmVOb2RlID0gX3JlZjJbMF0sXG4gICAgICAgIG1heWJlQXBwZWFyaW5nID0gX3JlZjJbMV07XG5cbiAgICB2YXIgdGltZW91dHMgPSB0aGlzLmdldFRpbWVvdXRzKCk7XG4gICAgdmFyIGVudGVyVGltZW91dCA9IGFwcGVhcmluZyA/IHRpbWVvdXRzLmFwcGVhciA6IHRpbWVvdXRzLmVudGVyOyAvLyBubyBlbnRlciBhbmltYXRpb24gc2tpcCByaWdodCB0byBFTlRFUkVEXG4gICAgLy8gaWYgd2UgYXJlIG1vdW50aW5nIGFuZCBydW5uaW5nIHRoaXMgaXQgbWVhbnMgYXBwZWFyIF9tdXN0XyBiZSBzZXRcblxuICAgIGlmICghbW91bnRpbmcgJiYgIWVudGVyIHx8IGNvbmZpZy5kaXNhYmxlZCkge1xuICAgICAgdGhpcy5zYWZlU2V0U3RhdGUoe1xuICAgICAgICBzdGF0dXM6IEVOVEVSRURcbiAgICAgIH0sIGZ1bmN0aW9uICgpIHtcbiAgICAgICAgX3RoaXMyLnByb3BzLm9uRW50ZXJlZChtYXliZU5vZGUpO1xuICAgICAgfSk7XG4gICAgICByZXR1cm47XG4gICAgfVxuXG4gICAgdGhpcy5wcm9wcy5vbkVudGVyKG1heWJlTm9kZSwgbWF5YmVBcHBlYXJpbmcpO1xuICAgIHRoaXMuc2FmZVNldFN0YXRlKHtcbiAgICAgIHN0YXR1czogRU5URVJJTkdcbiAgICB9LCBmdW5jdGlvbiAoKSB7XG4gICAgICBfdGhpczIucHJvcHMub25FbnRlcmluZyhtYXliZU5vZGUsIG1heWJlQXBwZWFyaW5nKTtcblxuICAgICAgX3RoaXMyLm9uVHJhbnNpdGlvbkVuZChlbnRlclRpbWVvdXQsIGZ1bmN0aW9uICgpIHtcbiAgICAgICAgX3RoaXMyLnNhZmVTZXRTdGF0ZSh7XG4gICAgICAgICAgc3RhdHVzOiBFTlRFUkVEXG4gICAgICAgIH0sIGZ1bmN0aW9uICgpIHtcbiAgICAgICAgICBfdGhpczIucHJvcHMub25FbnRlcmVkKG1heWJlTm9kZSwgbWF5YmVBcHBlYXJpbmcpO1xuICAgICAgICB9KTtcbiAgICAgIH0pO1xuICAgIH0pO1xuICB9O1xuXG4gIF9wcm90by5wZXJmb3JtRXhpdCA9IGZ1bmN0aW9uIHBlcmZvcm1FeGl0KCkge1xuICAgIHZhciBfdGhpczMgPSB0aGlzO1xuXG4gICAgdmFyIGV4aXQgPSB0aGlzLnByb3BzLmV4aXQ7XG4gICAgdmFyIHRpbWVvdXRzID0gdGhpcy5nZXRUaW1lb3V0cygpO1xuICAgIHZhciBtYXliZU5vZGUgPSB0aGlzLnByb3BzLm5vZGVSZWYgPyB1bmRlZmluZWQgOiBSZWFjdERPTS5maW5kRE9NTm9kZSh0aGlzKTsgLy8gbm8gZXhpdCBhbmltYXRpb24gc2tpcCByaWdodCB0byBFWElURURcblxuICAgIGlmICghZXhpdCB8fCBjb25maWcuZGlzYWJsZWQpIHtcbiAgICAgIHRoaXMuc2FmZVNldFN0YXRlKHtcbiAgICAgICAgc3RhdHVzOiBFWElURURcbiAgICAgIH0sIGZ1bmN0aW9uICgpIHtcbiAgICAgICAgX3RoaXMzLnByb3BzLm9uRXhpdGVkKG1heWJlTm9kZSk7XG4gICAgICB9KTtcbiAgICAgIHJldHVybjtcbiAgICB9XG5cbiAgICB0aGlzLnByb3BzLm9uRXhpdChtYXliZU5vZGUpO1xuICAgIHRoaXMuc2FmZVNldFN0YXRlKHtcbiAgICAgIHN0YXR1czogRVhJVElOR1xuICAgIH0sIGZ1bmN0aW9uICgpIHtcbiAgICAgIF90aGlzMy5wcm9wcy5vbkV4aXRpbmcobWF5YmVOb2RlKTtcblxuICAgICAgX3RoaXMzLm9uVHJhbnNpdGlvbkVuZCh0aW1lb3V0cy5leGl0LCBmdW5jdGlvbiAoKSB7XG4gICAgICAgIF90aGlzMy5zYWZlU2V0U3RhdGUoe1xuICAgICAgICAgIHN0YXR1czogRVhJVEVEXG4gICAgICAgIH0sIGZ1bmN0aW9uICgpIHtcbiAgICAgICAgICBfdGhpczMucHJvcHMub25FeGl0ZWQobWF5YmVOb2RlKTtcbiAgICAgICAgfSk7XG4gICAgICB9KTtcbiAgICB9KTtcbiAgfTtcblxuICBfcHJvdG8uY2FuY2VsTmV4dENhbGxiYWNrID0gZnVuY3Rpb24gY2FuY2VsTmV4dENhbGxiYWNrKCkge1xuICAgIGlmICh0aGlzLm5leHRDYWxsYmFjayAhPT0gbnVsbCkge1xuICAgICAgdGhpcy5uZXh0Q2FsbGJhY2suY2FuY2VsKCk7XG4gICAgICB0aGlzLm5leHRDYWxsYmFjayA9IG51bGw7XG4gICAgfVxuICB9O1xuXG4gIF9wcm90by5zYWZlU2V0U3RhdGUgPSBmdW5jdGlvbiBzYWZlU2V0U3RhdGUobmV4dFN0YXRlLCBjYWxsYmFjaykge1xuICAgIC8vIFRoaXMgc2hvdWxkbid0IGJlIG5lY2Vzc2FyeSwgYnV0IHRoZXJlIGFyZSB3ZWlyZCByYWNlIGNvbmRpdGlvbnMgd2l0aFxuICAgIC8vIHNldFN0YXRlIGNhbGxiYWNrcyBhbmQgdW5tb3VudGluZyBpbiB0ZXN0aW5nLCBzbyBhbHdheXMgbWFrZSBzdXJlIHRoYXRcbiAgICAvLyB3ZSBjYW4gY2FuY2VsIGFueSBwZW5kaW5nIHNldFN0YXRlIGNhbGxiYWNrcyBhZnRlciB3ZSB1bm1vdW50LlxuICAgIGNhbGxiYWNrID0gdGhpcy5zZXROZXh0Q2FsbGJhY2soY2FsbGJhY2spO1xuICAgIHRoaXMuc2V0U3RhdGUobmV4dFN0YXRlLCBjYWxsYmFjayk7XG4gIH07XG5cbiAgX3Byb3RvLnNldE5leHRDYWxsYmFjayA9IGZ1bmN0aW9uIHNldE5leHRDYWxsYmFjayhjYWxsYmFjaykge1xuICAgIHZhciBfdGhpczQgPSB0aGlzO1xuXG4gICAgdmFyIGFjdGl2ZSA9IHRydWU7XG5cbiAgICB0aGlzLm5leHRDYWxsYmFjayA9IGZ1bmN0aW9uIChldmVudCkge1xuICAgICAgaWYgKGFjdGl2ZSkge1xuICAgICAgICBhY3RpdmUgPSBmYWxzZTtcbiAgICAgICAgX3RoaXM0Lm5leHRDYWxsYmFjayA9IG51bGw7XG4gICAgICAgIGNhbGxiYWNrKGV2ZW50KTtcbiAgICAgIH1cbiAgICB9O1xuXG4gICAgdGhpcy5uZXh0Q2FsbGJhY2suY2FuY2VsID0gZnVuY3Rpb24gKCkge1xuICAgICAgYWN0aXZlID0gZmFsc2U7XG4gICAgfTtcblxuICAgIHJldHVybiB0aGlzLm5leHRDYWxsYmFjaztcbiAgfTtcblxuICBfcHJvdG8ub25UcmFuc2l0aW9uRW5kID0gZnVuY3Rpb24gb25UcmFuc2l0aW9uRW5kKHRpbWVvdXQsIGhhbmRsZXIpIHtcbiAgICB0aGlzLnNldE5leHRDYWxsYmFjayhoYW5kbGVyKTtcbiAgICB2YXIgbm9kZSA9IHRoaXMucHJvcHMubm9kZVJlZiA/IHRoaXMucHJvcHMubm9kZVJlZi5jdXJyZW50IDogUmVhY3RET00uZmluZERPTU5vZGUodGhpcyk7XG4gICAgdmFyIGRvZXNOb3RIYXZlVGltZW91dE9yTGlzdGVuZXIgPSB0aW1lb3V0ID09IG51bGwgJiYgIXRoaXMucHJvcHMuYWRkRW5kTGlzdGVuZXI7XG5cbiAgICBpZiAoIW5vZGUgfHwgZG9lc05vdEhhdmVUaW1lb3V0T3JMaXN0ZW5lcikge1xuICAgICAgc2V0VGltZW91dCh0aGlzLm5leHRDYWxsYmFjaywgMCk7XG4gICAgICByZXR1cm47XG4gICAgfVxuXG4gICAgaWYgKHRoaXMucHJvcHMuYWRkRW5kTGlzdGVuZXIpIHtcbiAgICAgIHZhciBfcmVmMyA9IHRoaXMucHJvcHMubm9kZVJlZiA/IFt0aGlzLm5leHRDYWxsYmFja10gOiBbbm9kZSwgdGhpcy5uZXh0Q2FsbGJhY2tdLFxuICAgICAgICAgIG1heWJlTm9kZSA9IF9yZWYzWzBdLFxuICAgICAgICAgIG1heWJlTmV4dENhbGxiYWNrID0gX3JlZjNbMV07XG5cbiAgICAgIHRoaXMucHJvcHMuYWRkRW5kTGlzdGVuZXIobWF5YmVOb2RlLCBtYXliZU5leHRDYWxsYmFjayk7XG4gICAgfVxuXG4gICAgaWYgKHRpbWVvdXQgIT0gbnVsbCkge1xuICAgICAgc2V0VGltZW91dCh0aGlzLm5leHRDYWxsYmFjaywgdGltZW91dCk7XG4gICAgfVxuICB9O1xuXG4gIF9wcm90by5yZW5kZXIgPSBmdW5jdGlvbiByZW5kZXIoKSB7XG4gICAgdmFyIHN0YXR1cyA9IHRoaXMuc3RhdGUuc3RhdHVzO1xuXG4gICAgaWYgKHN0YXR1cyA9PT0gVU5NT1VOVEVEKSB7XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG5cbiAgICB2YXIgX3RoaXMkcHJvcHMgPSB0aGlzLnByb3BzLFxuICAgICAgICBjaGlsZHJlbiA9IF90aGlzJHByb3BzLmNoaWxkcmVuLFxuICAgICAgICBfaW4gPSBfdGhpcyRwcm9wcy5pbixcbiAgICAgICAgX21vdW50T25FbnRlciA9IF90aGlzJHByb3BzLm1vdW50T25FbnRlcixcbiAgICAgICAgX3VubW91bnRPbkV4aXQgPSBfdGhpcyRwcm9wcy51bm1vdW50T25FeGl0LFxuICAgICAgICBfYXBwZWFyID0gX3RoaXMkcHJvcHMuYXBwZWFyLFxuICAgICAgICBfZW50ZXIgPSBfdGhpcyRwcm9wcy5lbnRlcixcbiAgICAgICAgX2V4aXQgPSBfdGhpcyRwcm9wcy5leGl0LFxuICAgICAgICBfdGltZW91dCA9IF90aGlzJHByb3BzLnRpbWVvdXQsXG4gICAgICAgIF9hZGRFbmRMaXN0ZW5lciA9IF90aGlzJHByb3BzLmFkZEVuZExpc3RlbmVyLFxuICAgICAgICBfb25FbnRlciA9IF90aGlzJHByb3BzLm9uRW50ZXIsXG4gICAgICAgIF9vbkVudGVyaW5nID0gX3RoaXMkcHJvcHMub25FbnRlcmluZyxcbiAgICAgICAgX29uRW50ZXJlZCA9IF90aGlzJHByb3BzLm9uRW50ZXJlZCxcbiAgICAgICAgX29uRXhpdCA9IF90aGlzJHByb3BzLm9uRXhpdCxcbiAgICAgICAgX29uRXhpdGluZyA9IF90aGlzJHByb3BzLm9uRXhpdGluZyxcbiAgICAgICAgX29uRXhpdGVkID0gX3RoaXMkcHJvcHMub25FeGl0ZWQsXG4gICAgICAgIF9ub2RlUmVmID0gX3RoaXMkcHJvcHMubm9kZVJlZixcbiAgICAgICAgY2hpbGRQcm9wcyA9IF9vYmplY3RXaXRob3V0UHJvcGVydGllc0xvb3NlKF90aGlzJHByb3BzLCBbXCJjaGlsZHJlblwiLCBcImluXCIsIFwibW91bnRPbkVudGVyXCIsIFwidW5tb3VudE9uRXhpdFwiLCBcImFwcGVhclwiLCBcImVudGVyXCIsIFwiZXhpdFwiLCBcInRpbWVvdXRcIiwgXCJhZGRFbmRMaXN0ZW5lclwiLCBcIm9uRW50ZXJcIiwgXCJvbkVudGVyaW5nXCIsIFwib25FbnRlcmVkXCIsIFwib25FeGl0XCIsIFwib25FeGl0aW5nXCIsIFwib25FeGl0ZWRcIiwgXCJub2RlUmVmXCJdKTtcblxuICAgIHJldHVybiAoXG4gICAgICAvKiNfX1BVUkVfXyovXG4gICAgICAvLyBhbGxvd3MgZm9yIG5lc3RlZCBUcmFuc2l0aW9uc1xuICAgICAgUmVhY3QuY3JlYXRlRWxlbWVudChUcmFuc2l0aW9uR3JvdXBDb250ZXh0LlByb3ZpZGVyLCB7XG4gICAgICAgIHZhbHVlOiBudWxsXG4gICAgICB9LCB0eXBlb2YgY2hpbGRyZW4gPT09ICdmdW5jdGlvbicgPyBjaGlsZHJlbihzdGF0dXMsIGNoaWxkUHJvcHMpIDogUmVhY3QuY2xvbmVFbGVtZW50KFJlYWN0LkNoaWxkcmVuLm9ubHkoY2hpbGRyZW4pLCBjaGlsZFByb3BzKSlcbiAgICApO1xuICB9O1xuXG4gIHJldHVybiBUcmFuc2l0aW9uO1xufShSZWFjdC5Db21wb25lbnQpO1xuXG5UcmFuc2l0aW9uLmNvbnRleHRUeXBlID0gVHJhbnNpdGlvbkdyb3VwQ29udGV4dDtcblRyYW5zaXRpb24ucHJvcFR5cGVzID0gcHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09IFwicHJvZHVjdGlvblwiID8ge1xuICAvKipcbiAgICogQSBSZWFjdCByZWZlcmVuY2UgdG8gRE9NIGVsZW1lbnQgdGhhdCBuZWVkIHRvIHRyYW5zaXRpb246XG4gICAqIGh0dHBzOi8vc3RhY2tvdmVyZmxvdy5jb20vYS81MTEyNzEzMC80NjcxOTMyXG4gICAqXG4gICAqICAgLSBXaGVuIGBub2RlUmVmYCBwcm9wIGlzIHVzZWQsIGBub2RlYCBpcyBub3QgcGFzc2VkIHRvIGNhbGxiYWNrIGZ1bmN0aW9uc1xuICAgKiAgICAgIChlLmcuIGBvbkVudGVyYCkgYmVjYXVzZSB1c2VyIGFscmVhZHkgaGFzIGRpcmVjdCBhY2Nlc3MgdG8gdGhlIG5vZGUuXG4gICAqICAgLSBXaGVuIGNoYW5naW5nIGBrZXlgIHByb3Agb2YgYFRyYW5zaXRpb25gIGluIGEgYFRyYW5zaXRpb25Hcm91cGAgYSBuZXdcbiAgICogICAgIGBub2RlUmVmYCBuZWVkIHRvIGJlIHByb3ZpZGVkIHRvIGBUcmFuc2l0aW9uYCB3aXRoIGNoYW5nZWQgYGtleWAgcHJvcFxuICAgKiAgICAgKHNlZVxuICAgKiAgICAgW3Rlc3QvQ1NTVHJhbnNpdGlvbi10ZXN0LmpzXShodHRwczovL2dpdGh1Yi5jb20vcmVhY3Rqcy9yZWFjdC10cmFuc2l0aW9uLWdyb3VwL2Jsb2IvMTM0MzVmODk3YjNhYjcxZjZlMTlkNzI0ZjE0NTU5NmY1OTEwNTgxYy90ZXN0L0NTU1RyYW5zaXRpb24tdGVzdC5qcyNMMzYyLUw0MzcpKS5cbiAgICovXG4gIG5vZGVSZWY6IFByb3BUeXBlcy5zaGFwZSh7XG4gICAgY3VycmVudDogdHlwZW9mIEVsZW1lbnQgPT09ICd1bmRlZmluZWQnID8gUHJvcFR5cGVzLmFueSA6IGZ1bmN0aW9uIChwcm9wVmFsdWUsIGtleSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSwgc2VjcmV0KSB7XG4gICAgICB2YXIgdmFsdWUgPSBwcm9wVmFsdWVba2V5XTtcbiAgICAgIHJldHVybiBQcm9wVHlwZXMuaW5zdGFuY2VPZih2YWx1ZSAmJiAnb3duZXJEb2N1bWVudCcgaW4gdmFsdWUgPyB2YWx1ZS5vd25lckRvY3VtZW50LmRlZmF1bHRWaWV3LkVsZW1lbnQgOiBFbGVtZW50KShwcm9wVmFsdWUsIGtleSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSwgc2VjcmV0KTtcbiAgICB9XG4gIH0pLFxuXG4gIC8qKlxuICAgKiBBIGBmdW5jdGlvbmAgY2hpbGQgY2FuIGJlIHVzZWQgaW5zdGVhZCBvZiBhIFJlYWN0IGVsZW1lbnQuIFRoaXMgZnVuY3Rpb24gaXNcbiAgICogY2FsbGVkIHdpdGggdGhlIGN1cnJlbnQgdHJhbnNpdGlvbiBzdGF0dXMgKGAnZW50ZXJpbmcnYCwgYCdlbnRlcmVkJ2AsXG4gICAqIGAnZXhpdGluZydgLCBgJ2V4aXRlZCdgKSwgd2hpY2ggY2FuIGJlIHVzZWQgdG8gYXBwbHkgY29udGV4dFxuICAgKiBzcGVjaWZpYyBwcm9wcyB0byBhIGNvbXBvbmVudC5cbiAgICpcbiAgICogYGBganN4XG4gICAqIDxUcmFuc2l0aW9uIGluPXt0aGlzLnN0YXRlLmlufSB0aW1lb3V0PXsxNTB9PlxuICAgKiAgIHtzdGF0ZSA9PiAoXG4gICAqICAgICA8TXlDb21wb25lbnQgY2xhc3NOYW1lPXtgZmFkZSBmYWRlLSR7c3RhdGV9YH0gLz5cbiAgICogICApfVxuICAgKiA8L1RyYW5zaXRpb24+XG4gICAqIGBgYFxuICAgKi9cbiAgY2hpbGRyZW46IFByb3BUeXBlcy5vbmVPZlR5cGUoW1Byb3BUeXBlcy5mdW5jLmlzUmVxdWlyZWQsIFByb3BUeXBlcy5lbGVtZW50LmlzUmVxdWlyZWRdKS5pc1JlcXVpcmVkLFxuXG4gIC8qKlxuICAgKiBTaG93IHRoZSBjb21wb25lbnQ7IHRyaWdnZXJzIHRoZSBlbnRlciBvciBleGl0IHN0YXRlc1xuICAgKi9cbiAgaW46IFByb3BUeXBlcy5ib29sLFxuXG4gIC8qKlxuICAgKiBCeSBkZWZhdWx0IHRoZSBjaGlsZCBjb21wb25lbnQgaXMgbW91bnRlZCBpbW1lZGlhdGVseSBhbG9uZyB3aXRoXG4gICAqIHRoZSBwYXJlbnQgYFRyYW5zaXRpb25gIGNvbXBvbmVudC4gSWYgeW91IHdhbnQgdG8gXCJsYXp5IG1vdW50XCIgdGhlIGNvbXBvbmVudCBvbiB0aGVcbiAgICogZmlyc3QgYGluPXt0cnVlfWAgeW91IGNhbiBzZXQgYG1vdW50T25FbnRlcmAuIEFmdGVyIHRoZSBmaXJzdCBlbnRlciB0cmFuc2l0aW9uIHRoZSBjb21wb25lbnQgd2lsbCBzdGF5XG4gICAqIG1vdW50ZWQsIGV2ZW4gb24gXCJleGl0ZWRcIiwgdW5sZXNzIHlvdSBhbHNvIHNwZWNpZnkgYHVubW91bnRPbkV4aXRgLlxuICAgKi9cbiAgbW91bnRPbkVudGVyOiBQcm9wVHlwZXMuYm9vbCxcblxuICAvKipcbiAgICogQnkgZGVmYXVsdCB0aGUgY2hpbGQgY29tcG9uZW50IHN0YXlzIG1vdW50ZWQgYWZ0ZXIgaXQgcmVhY2hlcyB0aGUgYCdleGl0ZWQnYCBzdGF0ZS5cbiAgICogU2V0IGB1bm1vdW50T25FeGl0YCBpZiB5b3UnZCBwcmVmZXIgdG8gdW5tb3VudCB0aGUgY29tcG9uZW50IGFmdGVyIGl0IGZpbmlzaGVzIGV4aXRpbmcuXG4gICAqL1xuICB1bm1vdW50T25FeGl0OiBQcm9wVHlwZXMuYm9vbCxcblxuICAvKipcbiAgICogQnkgZGVmYXVsdCB0aGUgY2hpbGQgY29tcG9uZW50IGRvZXMgbm90IHBlcmZvcm0gdGhlIGVudGVyIHRyYW5zaXRpb24gd2hlblxuICAgKiBpdCBmaXJzdCBtb3VudHMsIHJlZ2FyZGxlc3Mgb2YgdGhlIHZhbHVlIG9mIGBpbmAuIElmIHlvdSB3YW50IHRoaXNcbiAgICogYmVoYXZpb3IsIHNldCBib3RoIGBhcHBlYXJgIGFuZCBgaW5gIHRvIGB0cnVlYC5cbiAgICpcbiAgICogPiAqKk5vdGUqKjogdGhlcmUgYXJlIG5vIHNwZWNpYWwgYXBwZWFyIHN0YXRlcyBsaWtlIGBhcHBlYXJpbmdgL2BhcHBlYXJlZGAsIHRoaXMgcHJvcFxuICAgKiA+IG9ubHkgYWRkcyBhbiBhZGRpdGlvbmFsIGVudGVyIHRyYW5zaXRpb24uIEhvd2V2ZXIsIGluIHRoZVxuICAgKiA+IGA8Q1NTVHJhbnNpdGlvbj5gIGNvbXBvbmVudCB0aGF0IGZpcnN0IGVudGVyIHRyYW5zaXRpb24gZG9lcyByZXN1bHQgaW5cbiAgICogPiBhZGRpdGlvbmFsIGAuYXBwZWFyLSpgIGNsYXNzZXMsIHRoYXQgd2F5IHlvdSBjYW4gY2hvb3NlIHRvIHN0eWxlIGl0XG4gICAqID4gZGlmZmVyZW50bHkuXG4gICAqL1xuICBhcHBlYXI6IFByb3BUeXBlcy5ib29sLFxuXG4gIC8qKlxuICAgKiBFbmFibGUgb3IgZGlzYWJsZSBlbnRlciB0cmFuc2l0aW9ucy5cbiAgICovXG4gIGVudGVyOiBQcm9wVHlwZXMuYm9vbCxcblxuICAvKipcbiAgICogRW5hYmxlIG9yIGRpc2FibGUgZXhpdCB0cmFuc2l0aW9ucy5cbiAgICovXG4gIGV4aXQ6IFByb3BUeXBlcy5ib29sLFxuXG4gIC8qKlxuICAgKiBUaGUgZHVyYXRpb24gb2YgdGhlIHRyYW5zaXRpb24sIGluIG1pbGxpc2Vjb25kcy5cbiAgICogUmVxdWlyZWQgdW5sZXNzIGBhZGRFbmRMaXN0ZW5lcmAgaXMgcHJvdmlkZWQuXG4gICAqXG4gICAqIFlvdSBtYXkgc3BlY2lmeSBhIHNpbmdsZSB0aW1lb3V0IGZvciBhbGwgdHJhbnNpdGlvbnM6XG4gICAqXG4gICAqIGBgYGpzeFxuICAgKiB0aW1lb3V0PXs1MDB9XG4gICAqIGBgYFxuICAgKlxuICAgKiBvciBpbmRpdmlkdWFsbHk6XG4gICAqXG4gICAqIGBgYGpzeFxuICAgKiB0aW1lb3V0PXt7XG4gICAqICBhcHBlYXI6IDUwMCxcbiAgICogIGVudGVyOiAzMDAsXG4gICAqICBleGl0OiA1MDAsXG4gICAqIH19XG4gICAqIGBgYFxuICAgKlxuICAgKiAtIGBhcHBlYXJgIGRlZmF1bHRzIHRvIHRoZSB2YWx1ZSBvZiBgZW50ZXJgXG4gICAqIC0gYGVudGVyYCBkZWZhdWx0cyB0byBgMGBcbiAgICogLSBgZXhpdGAgZGVmYXVsdHMgdG8gYDBgXG4gICAqXG4gICAqIEB0eXBlIHtudW1iZXIgfCB7IGVudGVyPzogbnVtYmVyLCBleGl0PzogbnVtYmVyLCBhcHBlYXI/OiBudW1iZXIgfX1cbiAgICovXG4gIHRpbWVvdXQ6IGZ1bmN0aW9uIHRpbWVvdXQocHJvcHMpIHtcbiAgICB2YXIgcHQgPSB0aW1lb3V0c1NoYXBlO1xuICAgIGlmICghcHJvcHMuYWRkRW5kTGlzdGVuZXIpIHB0ID0gcHQuaXNSZXF1aXJlZDtcblxuICAgIGZvciAodmFyIF9sZW4gPSBhcmd1bWVudHMubGVuZ3RoLCBhcmdzID0gbmV3IEFycmF5KF9sZW4gPiAxID8gX2xlbiAtIDEgOiAwKSwgX2tleSA9IDE7IF9rZXkgPCBfbGVuOyBfa2V5KyspIHtcbiAgICAgIGFyZ3NbX2tleSAtIDFdID0gYXJndW1lbnRzW19rZXldO1xuICAgIH1cblxuICAgIHJldHVybiBwdC5hcHBseSh2b2lkIDAsIFtwcm9wc10uY29uY2F0KGFyZ3MpKTtcbiAgfSxcblxuICAvKipcbiAgICogQWRkIGEgY3VzdG9tIHRyYW5zaXRpb24gZW5kIHRyaWdnZXIuIENhbGxlZCB3aXRoIHRoZSB0cmFuc2l0aW9uaW5nXG4gICAqIERPTSBub2RlIGFuZCBhIGBkb25lYCBjYWxsYmFjay4gQWxsb3dzIGZvciBtb3JlIGZpbmUgZ3JhaW5lZCB0cmFuc2l0aW9uIGVuZFxuICAgKiBsb2dpYy4gVGltZW91dHMgYXJlIHN0aWxsIHVzZWQgYXMgYSBmYWxsYmFjayBpZiBwcm92aWRlZC5cbiAgICpcbiAgICogKipOb3RlKio6IHdoZW4gYG5vZGVSZWZgIHByb3AgaXMgcGFzc2VkLCBgbm9kZWAgaXMgbm90IHBhc3NlZC5cbiAgICpcbiAgICogYGBganN4XG4gICAqIGFkZEVuZExpc3RlbmVyPXsobm9kZSwgZG9uZSkgPT4ge1xuICAgKiAgIC8vIHVzZSB0aGUgY3NzIHRyYW5zaXRpb25lbmQgZXZlbnQgdG8gbWFyayB0aGUgZmluaXNoIG9mIGEgdHJhbnNpdGlvblxuICAgKiAgIG5vZGUuYWRkRXZlbnRMaXN0ZW5lcigndHJhbnNpdGlvbmVuZCcsIGRvbmUsIGZhbHNlKTtcbiAgICogfX1cbiAgICogYGBgXG4gICAqL1xuICBhZGRFbmRMaXN0ZW5lcjogUHJvcFR5cGVzLmZ1bmMsXG5cbiAgLyoqXG4gICAqIENhbGxiYWNrIGZpcmVkIGJlZm9yZSB0aGUgXCJlbnRlcmluZ1wiIHN0YXR1cyBpcyBhcHBsaWVkLiBBbiBleHRyYSBwYXJhbWV0ZXJcbiAgICogYGlzQXBwZWFyaW5nYCBpcyBzdXBwbGllZCB0byBpbmRpY2F0ZSBpZiB0aGUgZW50ZXIgc3RhZ2UgaXMgb2NjdXJyaW5nIG9uIHRoZSBpbml0aWFsIG1vdW50XG4gICAqXG4gICAqICoqTm90ZSoqOiB3aGVuIGBub2RlUmVmYCBwcm9wIGlzIHBhc3NlZCwgYG5vZGVgIGlzIG5vdCBwYXNzZWQuXG4gICAqXG4gICAqIEB0eXBlIEZ1bmN0aW9uKG5vZGU6IEh0bWxFbGVtZW50LCBpc0FwcGVhcmluZzogYm9vbCkgLT4gdm9pZFxuICAgKi9cbiAgb25FbnRlcjogUHJvcFR5cGVzLmZ1bmMsXG5cbiAgLyoqXG4gICAqIENhbGxiYWNrIGZpcmVkIGFmdGVyIHRoZSBcImVudGVyaW5nXCIgc3RhdHVzIGlzIGFwcGxpZWQuIEFuIGV4dHJhIHBhcmFtZXRlclxuICAgKiBgaXNBcHBlYXJpbmdgIGlzIHN1cHBsaWVkIHRvIGluZGljYXRlIGlmIHRoZSBlbnRlciBzdGFnZSBpcyBvY2N1cnJpbmcgb24gdGhlIGluaXRpYWwgbW91bnRcbiAgICpcbiAgICogKipOb3RlKio6IHdoZW4gYG5vZGVSZWZgIHByb3AgaXMgcGFzc2VkLCBgbm9kZWAgaXMgbm90IHBhc3NlZC5cbiAgICpcbiAgICogQHR5cGUgRnVuY3Rpb24obm9kZTogSHRtbEVsZW1lbnQsIGlzQXBwZWFyaW5nOiBib29sKVxuICAgKi9cbiAgb25FbnRlcmluZzogUHJvcFR5cGVzLmZ1bmMsXG5cbiAgLyoqXG4gICAqIENhbGxiYWNrIGZpcmVkIGFmdGVyIHRoZSBcImVudGVyZWRcIiBzdGF0dXMgaXMgYXBwbGllZC4gQW4gZXh0cmEgcGFyYW1ldGVyXG4gICAqIGBpc0FwcGVhcmluZ2AgaXMgc3VwcGxpZWQgdG8gaW5kaWNhdGUgaWYgdGhlIGVudGVyIHN0YWdlIGlzIG9jY3VycmluZyBvbiB0aGUgaW5pdGlhbCBtb3VudFxuICAgKlxuICAgKiAqKk5vdGUqKjogd2hlbiBgbm9kZVJlZmAgcHJvcCBpcyBwYXNzZWQsIGBub2RlYCBpcyBub3QgcGFzc2VkLlxuICAgKlxuICAgKiBAdHlwZSBGdW5jdGlvbihub2RlOiBIdG1sRWxlbWVudCwgaXNBcHBlYXJpbmc6IGJvb2wpIC0+IHZvaWRcbiAgICovXG4gIG9uRW50ZXJlZDogUHJvcFR5cGVzLmZ1bmMsXG5cbiAgLyoqXG4gICAqIENhbGxiYWNrIGZpcmVkIGJlZm9yZSB0aGUgXCJleGl0aW5nXCIgc3RhdHVzIGlzIGFwcGxpZWQuXG4gICAqXG4gICAqICoqTm90ZSoqOiB3aGVuIGBub2RlUmVmYCBwcm9wIGlzIHBhc3NlZCwgYG5vZGVgIGlzIG5vdCBwYXNzZWQuXG4gICAqXG4gICAqIEB0eXBlIEZ1bmN0aW9uKG5vZGU6IEh0bWxFbGVtZW50KSAtPiB2b2lkXG4gICAqL1xuICBvbkV4aXQ6IFByb3BUeXBlcy5mdW5jLFxuXG4gIC8qKlxuICAgKiBDYWxsYmFjayBmaXJlZCBhZnRlciB0aGUgXCJleGl0aW5nXCIgc3RhdHVzIGlzIGFwcGxpZWQuXG4gICAqXG4gICAqICoqTm90ZSoqOiB3aGVuIGBub2RlUmVmYCBwcm9wIGlzIHBhc3NlZCwgYG5vZGVgIGlzIG5vdCBwYXNzZWQuXG4gICAqXG4gICAqIEB0eXBlIEZ1bmN0aW9uKG5vZGU6IEh0bWxFbGVtZW50KSAtPiB2b2lkXG4gICAqL1xuICBvbkV4aXRpbmc6IFByb3BUeXBlcy5mdW5jLFxuXG4gIC8qKlxuICAgKiBDYWxsYmFjayBmaXJlZCBhZnRlciB0aGUgXCJleGl0ZWRcIiBzdGF0dXMgaXMgYXBwbGllZC5cbiAgICpcbiAgICogKipOb3RlKio6IHdoZW4gYG5vZGVSZWZgIHByb3AgaXMgcGFzc2VkLCBgbm9kZWAgaXMgbm90IHBhc3NlZFxuICAgKlxuICAgKiBAdHlwZSBGdW5jdGlvbihub2RlOiBIdG1sRWxlbWVudCkgLT4gdm9pZFxuICAgKi9cbiAgb25FeGl0ZWQ6IFByb3BUeXBlcy5mdW5jXG59IDoge307IC8vIE5hbWUgdGhlIGZ1bmN0aW9uIHNvIGl0IGlzIGNsZWFyZXIgaW4gdGhlIGRvY3VtZW50YXRpb25cblxuZnVuY3Rpb24gbm9vcCgpIHt9XG5cblRyYW5zaXRpb24uZGVmYXVsdFByb3BzID0ge1xuICBpbjogZmFsc2UsXG4gIG1vdW50T25FbnRlcjogZmFsc2UsXG4gIHVubW91bnRPbkV4aXQ6IGZhbHNlLFxuICBhcHBlYXI6IGZhbHNlLFxuICBlbnRlcjogdHJ1ZSxcbiAgZXhpdDogdHJ1ZSxcbiAgb25FbnRlcjogbm9vcCxcbiAgb25FbnRlcmluZzogbm9vcCxcbiAgb25FbnRlcmVkOiBub29wLFxuICBvbkV4aXQ6IG5vb3AsXG4gIG9uRXhpdGluZzogbm9vcCxcbiAgb25FeGl0ZWQ6IG5vb3Bcbn07XG5UcmFuc2l0aW9uLlVOTU9VTlRFRCA9IFVOTU9VTlRFRDtcblRyYW5zaXRpb24uRVhJVEVEID0gRVhJVEVEO1xuVHJhbnNpdGlvbi5FTlRFUklORyA9IEVOVEVSSU5HO1xuVHJhbnNpdGlvbi5FTlRFUkVEID0gRU5URVJFRDtcblRyYW5zaXRpb24uRVhJVElORyA9IEVYSVRJTkc7XG5leHBvcnQgZGVmYXVsdCBUcmFuc2l0aW9uOyIsImV4cG9ydCBkZWZhdWx0ICEhKHR5cGVvZiB3aW5kb3cgIT09ICd1bmRlZmluZWQnICYmIHdpbmRvdy5kb2N1bWVudCAmJiB3aW5kb3cuZG9jdW1lbnQuY3JlYXRlRWxlbWVudCk7IiwiLyogZXNsaW50LWRpc2FibGUgbm8tcmV0dXJuLWFzc2lnbiAqL1xuaW1wb3J0IGNhblVzZURPTSBmcm9tICcuL2NhblVzZURPTSc7XG5leHBvcnQgdmFyIG9wdGlvbnNTdXBwb3J0ZWQgPSBmYWxzZTtcbmV4cG9ydCB2YXIgb25jZVN1cHBvcnRlZCA9IGZhbHNlO1xuXG50cnkge1xuICB2YXIgb3B0aW9ucyA9IHtcbiAgICBnZXQgcGFzc2l2ZSgpIHtcbiAgICAgIHJldHVybiBvcHRpb25zU3VwcG9ydGVkID0gdHJ1ZTtcbiAgICB9LFxuXG4gICAgZ2V0IG9uY2UoKSB7XG4gICAgICAvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgbm8tbXVsdGktYXNzaWduXG4gICAgICByZXR1cm4gb25jZVN1cHBvcnRlZCA9IG9wdGlvbnNTdXBwb3J0ZWQgPSB0cnVlO1xuICAgIH1cblxuICB9O1xuXG4gIGlmIChjYW5Vc2VET00pIHtcbiAgICB3aW5kb3cuYWRkRXZlbnRMaXN0ZW5lcigndGVzdCcsIG9wdGlvbnMsIG9wdGlvbnMpO1xuICAgIHdpbmRvdy5yZW1vdmVFdmVudExpc3RlbmVyKCd0ZXN0Jywgb3B0aW9ucywgdHJ1ZSk7XG4gIH1cbn0gY2F0Y2ggKGUpIHtcbiAgLyogKi9cbn1cblxuLyoqXG4gKiBBbiBgYWRkRXZlbnRMaXN0ZW5lcmAgcG9ueWZpbGwsIHN1cHBvcnRzIHRoZSBgb25jZWAgb3B0aW9uXG4gKiBcbiAqIEBwYXJhbSBub2RlIHRoZSBlbGVtZW50XG4gKiBAcGFyYW0gZXZlbnROYW1lIHRoZSBldmVudCBuYW1lXG4gKiBAcGFyYW0gaGFuZGxlIHRoZSBoYW5kbGVyXG4gKiBAcGFyYW0gb3B0aW9ucyBldmVudCBvcHRpb25zXG4gKi9cbmZ1bmN0aW9uIGFkZEV2ZW50TGlzdGVuZXIobm9kZSwgZXZlbnROYW1lLCBoYW5kbGVyLCBvcHRpb25zKSB7XG4gIGlmIChvcHRpb25zICYmIHR5cGVvZiBvcHRpb25zICE9PSAnYm9vbGVhbicgJiYgIW9uY2VTdXBwb3J0ZWQpIHtcbiAgICB2YXIgb25jZSA9IG9wdGlvbnMub25jZSxcbiAgICAgICAgY2FwdHVyZSA9IG9wdGlvbnMuY2FwdHVyZTtcbiAgICB2YXIgd3JhcHBlZEhhbmRsZXIgPSBoYW5kbGVyO1xuXG4gICAgaWYgKCFvbmNlU3VwcG9ydGVkICYmIG9uY2UpIHtcbiAgICAgIHdyYXBwZWRIYW5kbGVyID0gaGFuZGxlci5fX29uY2UgfHwgZnVuY3Rpb24gb25jZUhhbmRsZXIoZXZlbnQpIHtcbiAgICAgICAgdGhpcy5yZW1vdmVFdmVudExpc3RlbmVyKGV2ZW50TmFtZSwgb25jZUhhbmRsZXIsIGNhcHR1cmUpO1xuICAgICAgICBoYW5kbGVyLmNhbGwodGhpcywgZXZlbnQpO1xuICAgICAgfTtcblxuICAgICAgaGFuZGxlci5fX29uY2UgPSB3cmFwcGVkSGFuZGxlcjtcbiAgICB9XG5cbiAgICBub2RlLmFkZEV2ZW50TGlzdGVuZXIoZXZlbnROYW1lLCB3cmFwcGVkSGFuZGxlciwgb3B0aW9uc1N1cHBvcnRlZCA/IG9wdGlvbnMgOiBjYXB0dXJlKTtcbiAgfVxuXG4gIG5vZGUuYWRkRXZlbnRMaXN0ZW5lcihldmVudE5hbWUsIGhhbmRsZXIsIG9wdGlvbnMpO1xufVxuXG5leHBvcnQgZGVmYXVsdCBhZGRFdmVudExpc3RlbmVyOyIsIi8qKlxuICogQSBgcmVtb3ZlRXZlbnRMaXN0ZW5lcmAgcG9ueWZpbGxcbiAqIFxuICogQHBhcmFtIG5vZGUgdGhlIGVsZW1lbnRcbiAqIEBwYXJhbSBldmVudE5hbWUgdGhlIGV2ZW50IG5hbWVcbiAqIEBwYXJhbSBoYW5kbGUgdGhlIGhhbmRsZXJcbiAqIEBwYXJhbSBvcHRpb25zIGV2ZW50IG9wdGlvbnNcbiAqL1xuZnVuY3Rpb24gcmVtb3ZlRXZlbnRMaXN0ZW5lcihub2RlLCBldmVudE5hbWUsIGhhbmRsZXIsIG9wdGlvbnMpIHtcbiAgdmFyIGNhcHR1cmUgPSBvcHRpb25zICYmIHR5cGVvZiBvcHRpb25zICE9PSAnYm9vbGVhbicgPyBvcHRpb25zLmNhcHR1cmUgOiBvcHRpb25zO1xuICBub2RlLnJlbW92ZUV2ZW50TGlzdGVuZXIoZXZlbnROYW1lLCBoYW5kbGVyLCBjYXB0dXJlKTtcblxuICBpZiAoaGFuZGxlci5fX29uY2UpIHtcbiAgICBub2RlLnJlbW92ZUV2ZW50TGlzdGVuZXIoZXZlbnROYW1lLCBoYW5kbGVyLl9fb25jZSwgY2FwdHVyZSk7XG4gIH1cbn1cblxuZXhwb3J0IGRlZmF1bHQgcmVtb3ZlRXZlbnRMaXN0ZW5lcjsiLCJpbXBvcnQgYWRkRXZlbnRMaXN0ZW5lciBmcm9tICcuL2FkZEV2ZW50TGlzdGVuZXInO1xuaW1wb3J0IHJlbW92ZUV2ZW50TGlzdGVuZXIgZnJvbSAnLi9yZW1vdmVFdmVudExpc3RlbmVyJztcblxuZnVuY3Rpb24gbGlzdGVuKG5vZGUsIGV2ZW50TmFtZSwgaGFuZGxlciwgb3B0aW9ucykge1xuICBhZGRFdmVudExpc3RlbmVyKG5vZGUsIGV2ZW50TmFtZSwgaGFuZGxlciwgb3B0aW9ucyk7XG4gIHJldHVybiBmdW5jdGlvbiAoKSB7XG4gICAgcmVtb3ZlRXZlbnRMaXN0ZW5lcihub2RlLCBldmVudE5hbWUsIGhhbmRsZXIsIG9wdGlvbnMpO1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBsaXN0ZW47IiwiLyoqXG4gKiBUcmlnZ2VycyBhbiBldmVudCBvbiBhIGdpdmVuIGVsZW1lbnQuXG4gKiBcbiAqIEBwYXJhbSBub2RlIHRoZSBlbGVtZW50XG4gKiBAcGFyYW0gZXZlbnROYW1lIHRoZSBldmVudCBuYW1lIHRvIHRyaWdnZXJcbiAqIEBwYXJhbSBidWJibGVzIHdoZXRoZXIgdGhlIGV2ZW50IHNob3VsZCBidWJibGUgdXBcbiAqIEBwYXJhbSBjYW5jZWxhYmxlIHdoZXRoZXIgdGhlIGV2ZW50IHNob3VsZCBiZSBjYW5jZWxhYmxlXG4gKi9cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIHRyaWdnZXJFdmVudChub2RlLCBldmVudE5hbWUsIGJ1YmJsZXMsIGNhbmNlbGFibGUpIHtcbiAgaWYgKGJ1YmJsZXMgPT09IHZvaWQgMCkge1xuICAgIGJ1YmJsZXMgPSBmYWxzZTtcbiAgfVxuXG4gIGlmIChjYW5jZWxhYmxlID09PSB2b2lkIDApIHtcbiAgICBjYW5jZWxhYmxlID0gdHJ1ZTtcbiAgfVxuXG4gIGlmIChub2RlKSB7XG4gICAgdmFyIGV2ZW50ID0gZG9jdW1lbnQuY3JlYXRlRXZlbnQoJ0hUTUxFdmVudHMnKTtcbiAgICBldmVudC5pbml0RXZlbnQoZXZlbnROYW1lLCBidWJibGVzLCBjYW5jZWxhYmxlKTtcbiAgICBub2RlLmRpc3BhdGNoRXZlbnQoZXZlbnQpO1xuICB9XG59IiwiaW1wb3J0IGNzcyBmcm9tICcuL2Nzcyc7XG5pbXBvcnQgbGlzdGVuIGZyb20gJy4vbGlzdGVuJztcbmltcG9ydCB0cmlnZ2VyRXZlbnQgZnJvbSAnLi90cmlnZ2VyRXZlbnQnO1xuXG5mdW5jdGlvbiBwYXJzZUR1cmF0aW9uKG5vZGUpIHtcbiAgdmFyIHN0ciA9IGNzcyhub2RlLCAndHJhbnNpdGlvbkR1cmF0aW9uJykgfHwgJyc7XG4gIHZhciBtdWx0ID0gc3RyLmluZGV4T2YoJ21zJykgPT09IC0xID8gMTAwMCA6IDE7XG4gIHJldHVybiBwYXJzZUZsb2F0KHN0cikgKiBtdWx0O1xufVxuXG5mdW5jdGlvbiBlbXVsYXRlVHJhbnNpdGlvbkVuZChlbGVtZW50LCBkdXJhdGlvbiwgcGFkZGluZykge1xuICBpZiAocGFkZGluZyA9PT0gdm9pZCAwKSB7XG4gICAgcGFkZGluZyA9IDU7XG4gIH1cblxuICB2YXIgY2FsbGVkID0gZmFsc2U7XG4gIHZhciBoYW5kbGUgPSBzZXRUaW1lb3V0KGZ1bmN0aW9uICgpIHtcbiAgICBpZiAoIWNhbGxlZCkgdHJpZ2dlckV2ZW50KGVsZW1lbnQsICd0cmFuc2l0aW9uZW5kJywgdHJ1ZSk7XG4gIH0sIGR1cmF0aW9uICsgcGFkZGluZyk7XG4gIHZhciByZW1vdmUgPSBsaXN0ZW4oZWxlbWVudCwgJ3RyYW5zaXRpb25lbmQnLCBmdW5jdGlvbiAoKSB7XG4gICAgY2FsbGVkID0gdHJ1ZTtcbiAgfSwge1xuICAgIG9uY2U6IHRydWVcbiAgfSk7XG4gIHJldHVybiBmdW5jdGlvbiAoKSB7XG4gICAgY2xlYXJUaW1lb3V0KGhhbmRsZSk7XG4gICAgcmVtb3ZlKCk7XG4gIH07XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIHRyYW5zaXRpb25FbmQoZWxlbWVudCwgaGFuZGxlciwgZHVyYXRpb24sIHBhZGRpbmcpIHtcbiAgaWYgKGR1cmF0aW9uID09IG51bGwpIGR1cmF0aW9uID0gcGFyc2VEdXJhdGlvbihlbGVtZW50KSB8fCAwO1xuICB2YXIgcmVtb3ZlRW11bGF0ZSA9IGVtdWxhdGVUcmFuc2l0aW9uRW5kKGVsZW1lbnQsIGR1cmF0aW9uLCBwYWRkaW5nKTtcbiAgdmFyIHJlbW92ZSA9IGxpc3RlbihlbGVtZW50LCAndHJhbnNpdGlvbmVuZCcsIGhhbmRsZXIpO1xuICByZXR1cm4gZnVuY3Rpb24gKCkge1xuICAgIHJlbW92ZUVtdWxhdGUoKTtcbiAgICByZW1vdmUoKTtcbiAgfTtcbn0iLCJpbXBvcnQgY3NzIGZyb20gJ2RvbS1oZWxwZXJzL2Nzcyc7XG5pbXBvcnQgdHJhbnNpdGlvbkVuZCBmcm9tICdkb20taGVscGVycy90cmFuc2l0aW9uRW5kJztcbmZ1bmN0aW9uIHBhcnNlRHVyYXRpb24obm9kZSwgcHJvcGVydHkpIHtcbiAgY29uc3Qgc3RyID0gY3NzKG5vZGUsIHByb3BlcnR5KSB8fCAnJztcbiAgY29uc3QgbXVsdCA9IHN0ci5pbmRleE9mKCdtcycpID09PSAtMSA/IDEwMDAgOiAxO1xuICByZXR1cm4gcGFyc2VGbG9hdChzdHIpICogbXVsdDtcbn1cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIHRyYW5zaXRpb25FbmRMaXN0ZW5lcihlbGVtZW50LCBoYW5kbGVyKSB7XG4gIGNvbnN0IGR1cmF0aW9uID0gcGFyc2VEdXJhdGlvbihlbGVtZW50LCAndHJhbnNpdGlvbkR1cmF0aW9uJyk7XG4gIGNvbnN0IGRlbGF5ID0gcGFyc2VEdXJhdGlvbihlbGVtZW50LCAndHJhbnNpdGlvbkRlbGF5Jyk7XG4gIGNvbnN0IHJlbW92ZSA9IHRyYW5zaXRpb25FbmQoZWxlbWVudCwgZSA9PiB7XG4gICAgaWYgKGUudGFyZ2V0ID09PSBlbGVtZW50KSB7XG4gICAgICByZW1vdmUoKTtcbiAgICAgIGhhbmRsZXIoZSk7XG4gICAgfVxuICB9LCBkdXJhdGlvbiArIGRlbGF5KTtcbn0iLCIvKipcbiAqIFNhZmUgY2hhaW5lZCBmdW5jdGlvblxuICpcbiAqIFdpbGwgb25seSBjcmVhdGUgYSBuZXcgZnVuY3Rpb24gaWYgbmVlZGVkLFxuICogb3RoZXJ3aXNlIHdpbGwgcGFzcyBiYWNrIGV4aXN0aW5nIGZ1bmN0aW9ucyBvciBudWxsLlxuICpcbiAqIEBwYXJhbSB7ZnVuY3Rpb259IGZ1bmN0aW9ucyB0byBjaGFpblxuICogQHJldHVybnMge2Z1bmN0aW9ufG51bGx9XG4gKi9cbmZ1bmN0aW9uIGNyZWF0ZUNoYWluZWRGdW5jdGlvbiguLi5mdW5jcykge1xuICByZXR1cm4gZnVuY3MuZmlsdGVyKGYgPT4gZiAhPSBudWxsKS5yZWR1Y2UoKGFjYywgZikgPT4ge1xuICAgIGlmICh0eXBlb2YgZiAhPT0gJ2Z1bmN0aW9uJykge1xuICAgICAgdGhyb3cgbmV3IEVycm9yKCdJbnZhbGlkIEFyZ3VtZW50IFR5cGUsIG11c3Qgb25seSBwcm92aWRlIGZ1bmN0aW9ucywgdW5kZWZpbmVkLCBvciBudWxsLicpO1xuICAgIH1cbiAgICBpZiAoYWNjID09PSBudWxsKSByZXR1cm4gZjtcbiAgICByZXR1cm4gZnVuY3Rpb24gY2hhaW5lZEZ1bmN0aW9uKC4uLmFyZ3MpIHtcbiAgICAgIC8vIEB0cy1pZ25vcmVcbiAgICAgIGFjYy5hcHBseSh0aGlzLCBhcmdzKTtcbiAgICAgIC8vIEB0cy1pZ25vcmVcbiAgICAgIGYuYXBwbHkodGhpcywgYXJncyk7XG4gICAgfTtcbiAgfSwgbnVsbCk7XG59XG5leHBvcnQgZGVmYXVsdCBjcmVhdGVDaGFpbmVkRnVuY3Rpb247IiwiLy8gcmVhZGluZyBhIGRpbWVuc2lvbiBwcm9wIHdpbGwgY2F1c2UgdGhlIGJyb3dzZXIgdG8gcmVjYWxjdWxhdGUsXG4vLyB3aGljaCB3aWxsIGxldCBvdXIgYW5pbWF0aW9ucyB3b3JrXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiB0cmlnZ2VyQnJvd3NlclJlZmxvdyhub2RlKSB7XG4gIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBAdHlwZXNjcmlwdC1lc2xpbnQvbm8tdW51c2VkLWV4cHJlc3Npb25zXG4gIG5vZGUub2Zmc2V0SGVpZ2h0O1xufSIsImltcG9ydCB7IHVzZU1lbW8gfSBmcm9tICdyZWFjdCc7XG5cbnZhciB0b0ZuUmVmID0gZnVuY3Rpb24gdG9GblJlZihyZWYpIHtcbiAgcmV0dXJuICFyZWYgfHwgdHlwZW9mIHJlZiA9PT0gJ2Z1bmN0aW9uJyA/IHJlZiA6IGZ1bmN0aW9uICh2YWx1ZSkge1xuICAgIHJlZi5jdXJyZW50ID0gdmFsdWU7XG4gIH07XG59O1xuXG5leHBvcnQgZnVuY3Rpb24gbWVyZ2VSZWZzKHJlZkEsIHJlZkIpIHtcbiAgdmFyIGEgPSB0b0ZuUmVmKHJlZkEpO1xuICB2YXIgYiA9IHRvRm5SZWYocmVmQik7XG4gIHJldHVybiBmdW5jdGlvbiAodmFsdWUpIHtcbiAgICBpZiAoYSkgYSh2YWx1ZSk7XG4gICAgaWYgKGIpIGIodmFsdWUpO1xuICB9O1xufVxuLyoqXG4gKiBDcmVhdGUgYW5kIHJldHVybnMgYSBzaW5nbGUgY2FsbGJhY2sgcmVmIGNvbXBvc2VkIGZyb20gdHdvIG90aGVyIFJlZnMuXG4gKlxuICogYGBgdHN4XG4gKiBjb25zdCBCdXR0b24gPSBSZWFjdC5mb3J3YXJkUmVmKChwcm9wcywgcmVmKSA9PiB7XG4gKiAgIGNvbnN0IFtlbGVtZW50LCBhdHRhY2hSZWZdID0gdXNlQ2FsbGJhY2tSZWY8SFRNTEJ1dHRvbkVsZW1lbnQ+KCk7XG4gKiAgIGNvbnN0IG1lcmdlZFJlZiA9IHVzZU1lcmdlZFJlZnMocmVmLCBhdHRhY2hSZWYpO1xuICpcbiAqICAgcmV0dXJuIDxidXR0b24gcmVmPXttZXJnZWRSZWZ9IHsuLi5wcm9wc30vPlxuICogfSlcbiAqIGBgYFxuICpcbiAqIEBwYXJhbSByZWZBIEEgQ2FsbGJhY2sgb3IgbXV0YWJsZSBSZWZcbiAqIEBwYXJhbSByZWZCIEEgQ2FsbGJhY2sgb3IgbXV0YWJsZSBSZWZcbiAqIEBjYXRlZ29yeSByZWZzXG4gKi9cblxuZnVuY3Rpb24gdXNlTWVyZ2VkUmVmcyhyZWZBLCByZWZCKSB7XG4gIHJldHVybiB1c2VNZW1vKGZ1bmN0aW9uICgpIHtcbiAgICByZXR1cm4gbWVyZ2VSZWZzKHJlZkEsIHJlZkIpO1xuICB9LCBbcmVmQSwgcmVmQl0pO1xufVxuXG5leHBvcnQgZGVmYXVsdCB1c2VNZXJnZWRSZWZzOyIsImltcG9ydCBSZWFjdERPTSBmcm9tICdyZWFjdC1kb20nO1xuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gc2FmZUZpbmRET01Ob2RlKGNvbXBvbmVudE9yRWxlbWVudCkge1xuICBpZiAoY29tcG9uZW50T3JFbGVtZW50ICYmICdzZXRTdGF0ZScgaW4gY29tcG9uZW50T3JFbGVtZW50KSB7XG4gICAgcmV0dXJuIFJlYWN0RE9NLmZpbmRET01Ob2RlKGNvbXBvbmVudE9yRWxlbWVudCk7XG4gIH1cbiAgcmV0dXJuIGNvbXBvbmVudE9yRWxlbWVudCAhPSBudWxsID8gY29tcG9uZW50T3JFbGVtZW50IDogbnVsbDtcbn0iLCJpbXBvcnQgUmVhY3QsIHsgdXNlQ2FsbGJhY2ssIHVzZVJlZiB9IGZyb20gJ3JlYWN0JztcbmltcG9ydCBUcmFuc2l0aW9uIGZyb20gJ3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvVHJhbnNpdGlvbic7XG5pbXBvcnQgdXNlTWVyZ2VkUmVmcyBmcm9tICdAcmVzdGFydC9ob29rcy91c2VNZXJnZWRSZWZzJztcbmltcG9ydCBzYWZlRmluZERPTU5vZGUgZnJvbSAnLi9zYWZlRmluZERPTU5vZGUnO1xuaW1wb3J0IHsganN4IGFzIF9qc3ggfSBmcm9tIFwicmVhY3QvanN4LXJ1bnRpbWVcIjtcbi8vIE5vcm1hbGl6ZXMgVHJhbnNpdGlvbiBjYWxsYmFja3Mgd2hlbiBub2RlUmVmIGlzIHVzZWQuXG5jb25zdCBUcmFuc2l0aW9uV3JhcHBlciA9IC8qI19fUFVSRV9fKi9SZWFjdC5mb3J3YXJkUmVmKCh7XG4gIG9uRW50ZXIsXG4gIG9uRW50ZXJpbmcsXG4gIG9uRW50ZXJlZCxcbiAgb25FeGl0LFxuICBvbkV4aXRpbmcsXG4gIG9uRXhpdGVkLFxuICBhZGRFbmRMaXN0ZW5lcixcbiAgY2hpbGRyZW4sXG4gIGNoaWxkUmVmLFxuICAuLi5wcm9wc1xufSwgcmVmKSA9PiB7XG4gIGNvbnN0IG5vZGVSZWYgPSB1c2VSZWYobnVsbCk7XG4gIGNvbnN0IG1lcmdlZFJlZiA9IHVzZU1lcmdlZFJlZnMobm9kZVJlZiwgY2hpbGRSZWYpO1xuICBjb25zdCBhdHRhY2hSZWYgPSByID0+IHtcbiAgICBtZXJnZWRSZWYoc2FmZUZpbmRET01Ob2RlKHIpKTtcbiAgfTtcbiAgY29uc3Qgbm9ybWFsaXplID0gY2FsbGJhY2sgPT4gcGFyYW0gPT4ge1xuICAgIGlmIChjYWxsYmFjayAmJiBub2RlUmVmLmN1cnJlbnQpIHtcbiAgICAgIGNhbGxiYWNrKG5vZGVSZWYuY3VycmVudCwgcGFyYW0pO1xuICAgIH1cbiAgfTtcblxuICAvKiBlc2xpbnQtZGlzYWJsZSByZWFjdC1ob29rcy9leGhhdXN0aXZlLWRlcHMgKi9cbiAgY29uc3QgaGFuZGxlRW50ZXIgPSB1c2VDYWxsYmFjayhub3JtYWxpemUob25FbnRlciksIFtvbkVudGVyXSk7XG4gIGNvbnN0IGhhbmRsZUVudGVyaW5nID0gdXNlQ2FsbGJhY2sobm9ybWFsaXplKG9uRW50ZXJpbmcpLCBbb25FbnRlcmluZ10pO1xuICBjb25zdCBoYW5kbGVFbnRlcmVkID0gdXNlQ2FsbGJhY2sobm9ybWFsaXplKG9uRW50ZXJlZCksIFtvbkVudGVyZWRdKTtcbiAgY29uc3QgaGFuZGxlRXhpdCA9IHVzZUNhbGxiYWNrKG5vcm1hbGl6ZShvbkV4aXQpLCBbb25FeGl0XSk7XG4gIGNvbnN0IGhhbmRsZUV4aXRpbmcgPSB1c2VDYWxsYmFjayhub3JtYWxpemUob25FeGl0aW5nKSwgW29uRXhpdGluZ10pO1xuICBjb25zdCBoYW5kbGVFeGl0ZWQgPSB1c2VDYWxsYmFjayhub3JtYWxpemUob25FeGl0ZWQpLCBbb25FeGl0ZWRdKTtcbiAgY29uc3QgaGFuZGxlQWRkRW5kTGlzdGVuZXIgPSB1c2VDYWxsYmFjayhub3JtYWxpemUoYWRkRW5kTGlzdGVuZXIpLCBbYWRkRW5kTGlzdGVuZXJdKTtcbiAgLyogZXNsaW50LWVuYWJsZSByZWFjdC1ob29rcy9leGhhdXN0aXZlLWRlcHMgKi9cblxuICByZXR1cm4gLyojX19QVVJFX18qL19qc3goVHJhbnNpdGlvbiwge1xuICAgIHJlZjogcmVmLFxuICAgIC4uLnByb3BzLFxuICAgIG9uRW50ZXI6IGhhbmRsZUVudGVyLFxuICAgIG9uRW50ZXJlZDogaGFuZGxlRW50ZXJlZCxcbiAgICBvbkVudGVyaW5nOiBoYW5kbGVFbnRlcmluZyxcbiAgICBvbkV4aXQ6IGhhbmRsZUV4aXQsXG4gICAgb25FeGl0ZWQ6IGhhbmRsZUV4aXRlZCxcbiAgICBvbkV4aXRpbmc6IGhhbmRsZUV4aXRpbmcsXG4gICAgYWRkRW5kTGlzdGVuZXI6IGhhbmRsZUFkZEVuZExpc3RlbmVyLFxuICAgIG5vZGVSZWY6IG5vZGVSZWYsXG4gICAgY2hpbGRyZW46IHR5cGVvZiBjaGlsZHJlbiA9PT0gJ2Z1bmN0aW9uJyA/IChzdGF0dXMsIGlubmVyUHJvcHMpID0+IGNoaWxkcmVuKHN0YXR1cywge1xuICAgICAgLi4uaW5uZXJQcm9wcyxcbiAgICAgIHJlZjogYXR0YWNoUmVmXG4gICAgfSkgOiAvKiNfX1BVUkVfXyovUmVhY3QuY2xvbmVFbGVtZW50KGNoaWxkcmVuLCB7XG4gICAgICByZWY6IGF0dGFjaFJlZlxuICAgIH0pXG4gIH0pO1xufSk7XG5leHBvcnQgZGVmYXVsdCBUcmFuc2l0aW9uV3JhcHBlcjsiLCJpbXBvcnQgY2xhc3NOYW1lcyBmcm9tICdjbGFzc25hbWVzJztcbmltcG9ydCBjc3MgZnJvbSAnZG9tLWhlbHBlcnMvY3NzJztcbmltcG9ydCBSZWFjdCwgeyB1c2VNZW1vIH0gZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsgRU5URVJFRCwgRU5URVJJTkcsIEVYSVRFRCwgRVhJVElORyB9IGZyb20gJ3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvVHJhbnNpdGlvbic7XG5pbXBvcnQgdHJhbnNpdGlvbkVuZExpc3RlbmVyIGZyb20gJy4vdHJhbnNpdGlvbkVuZExpc3RlbmVyJztcbmltcG9ydCBjcmVhdGVDaGFpbmVkRnVuY3Rpb24gZnJvbSAnLi9jcmVhdGVDaGFpbmVkRnVuY3Rpb24nO1xuaW1wb3J0IHRyaWdnZXJCcm93c2VyUmVmbG93IGZyb20gJy4vdHJpZ2dlckJyb3dzZXJSZWZsb3cnO1xuaW1wb3J0IFRyYW5zaXRpb25XcmFwcGVyIGZyb20gJy4vVHJhbnNpdGlvbldyYXBwZXInO1xuaW1wb3J0IHsganN4IGFzIF9qc3ggfSBmcm9tIFwicmVhY3QvanN4LXJ1bnRpbWVcIjtcbmNvbnN0IE1BUkdJTlMgPSB7XG4gIGhlaWdodDogWydtYXJnaW5Ub3AnLCAnbWFyZ2luQm90dG9tJ10sXG4gIHdpZHRoOiBbJ21hcmdpbkxlZnQnLCAnbWFyZ2luUmlnaHQnXVxufTtcbmZ1bmN0aW9uIGdldERlZmF1bHREaW1lbnNpb25WYWx1ZShkaW1lbnNpb24sIGVsZW0pIHtcbiAgY29uc3Qgb2Zmc2V0ID0gYG9mZnNldCR7ZGltZW5zaW9uWzBdLnRvVXBwZXJDYXNlKCl9JHtkaW1lbnNpb24uc2xpY2UoMSl9YDtcbiAgY29uc3QgdmFsdWUgPSBlbGVtW29mZnNldF07XG4gIGNvbnN0IG1hcmdpbnMgPSBNQVJHSU5TW2RpbWVuc2lvbl07XG4gIHJldHVybiB2YWx1ZSArXG4gIC8vIEB0cy1pZ25vcmVcbiAgcGFyc2VJbnQoY3NzKGVsZW0sIG1hcmdpbnNbMF0pLCAxMCkgK1xuICAvLyBAdHMtaWdub3JlXG4gIHBhcnNlSW50KGNzcyhlbGVtLCBtYXJnaW5zWzFdKSwgMTApO1xufVxuY29uc3QgY29sbGFwc2VTdHlsZXMgPSB7XG4gIFtFWElURURdOiAnY29sbGFwc2UnLFxuICBbRVhJVElOR106ICdjb2xsYXBzaW5nJyxcbiAgW0VOVEVSSU5HXTogJ2NvbGxhcHNpbmcnLFxuICBbRU5URVJFRF06ICdjb2xsYXBzZSBzaG93J1xufTtcbmNvbnN0IGRlZmF1bHRQcm9wcyA9IHtcbiAgaW46IGZhbHNlLFxuICB0aW1lb3V0OiAzMDAsXG4gIG1vdW50T25FbnRlcjogZmFsc2UsXG4gIHVubW91bnRPbkV4aXQ6IGZhbHNlLFxuICBhcHBlYXI6IGZhbHNlLFxuICBnZXREaW1lbnNpb25WYWx1ZTogZ2V0RGVmYXVsdERpbWVuc2lvblZhbHVlXG59O1xuY29uc3QgQ29sbGFwc2UgPSAvKiNfX1BVUkVfXyovUmVhY3QuZm9yd2FyZFJlZigoe1xuICBvbkVudGVyLFxuICBvbkVudGVyaW5nLFxuICBvbkVudGVyZWQsXG4gIG9uRXhpdCxcbiAgb25FeGl0aW5nLFxuICBjbGFzc05hbWUsXG4gIGNoaWxkcmVuLFxuICBkaW1lbnNpb24gPSAnaGVpZ2h0JyxcbiAgZ2V0RGltZW5zaW9uVmFsdWUgPSBnZXREZWZhdWx0RGltZW5zaW9uVmFsdWUsXG4gIC4uLnByb3BzXG59LCByZWYpID0+IHtcbiAgLyogQ29tcHV0ZSBkaW1lbnNpb24gKi9cbiAgY29uc3QgY29tcHV0ZWREaW1lbnNpb24gPSB0eXBlb2YgZGltZW5zaW9uID09PSAnZnVuY3Rpb24nID8gZGltZW5zaW9uKCkgOiBkaW1lbnNpb247XG5cbiAgLyogLS0gRXhwYW5kaW5nIC0tICovXG4gIGNvbnN0IGhhbmRsZUVudGVyID0gdXNlTWVtbygoKSA9PiBjcmVhdGVDaGFpbmVkRnVuY3Rpb24oZWxlbSA9PiB7XG4gICAgZWxlbS5zdHlsZVtjb21wdXRlZERpbWVuc2lvbl0gPSAnMCc7XG4gIH0sIG9uRW50ZXIpLCBbY29tcHV0ZWREaW1lbnNpb24sIG9uRW50ZXJdKTtcbiAgY29uc3QgaGFuZGxlRW50ZXJpbmcgPSB1c2VNZW1vKCgpID0+IGNyZWF0ZUNoYWluZWRGdW5jdGlvbihlbGVtID0+IHtcbiAgICBjb25zdCBzY3JvbGwgPSBgc2Nyb2xsJHtjb21wdXRlZERpbWVuc2lvblswXS50b1VwcGVyQ2FzZSgpfSR7Y29tcHV0ZWREaW1lbnNpb24uc2xpY2UoMSl9YDtcbiAgICBlbGVtLnN0eWxlW2NvbXB1dGVkRGltZW5zaW9uXSA9IGAke2VsZW1bc2Nyb2xsXX1weGA7XG4gIH0sIG9uRW50ZXJpbmcpLCBbY29tcHV0ZWREaW1lbnNpb24sIG9uRW50ZXJpbmddKTtcbiAgY29uc3QgaGFuZGxlRW50ZXJlZCA9IHVzZU1lbW8oKCkgPT4gY3JlYXRlQ2hhaW5lZEZ1bmN0aW9uKGVsZW0gPT4ge1xuICAgIGVsZW0uc3R5bGVbY29tcHV0ZWREaW1lbnNpb25dID0gbnVsbDtcbiAgfSwgb25FbnRlcmVkKSwgW2NvbXB1dGVkRGltZW5zaW9uLCBvbkVudGVyZWRdKTtcblxuICAvKiAtLSBDb2xsYXBzaW5nIC0tICovXG4gIGNvbnN0IGhhbmRsZUV4aXQgPSB1c2VNZW1vKCgpID0+IGNyZWF0ZUNoYWluZWRGdW5jdGlvbihlbGVtID0+IHtcbiAgICBlbGVtLnN0eWxlW2NvbXB1dGVkRGltZW5zaW9uXSA9IGAke2dldERpbWVuc2lvblZhbHVlKGNvbXB1dGVkRGltZW5zaW9uLCBlbGVtKX1weGA7XG4gICAgdHJpZ2dlckJyb3dzZXJSZWZsb3coZWxlbSk7XG4gIH0sIG9uRXhpdCksIFtvbkV4aXQsIGdldERpbWVuc2lvblZhbHVlLCBjb21wdXRlZERpbWVuc2lvbl0pO1xuICBjb25zdCBoYW5kbGVFeGl0aW5nID0gdXNlTWVtbygoKSA9PiBjcmVhdGVDaGFpbmVkRnVuY3Rpb24oZWxlbSA9PiB7XG4gICAgZWxlbS5zdHlsZVtjb21wdXRlZERpbWVuc2lvbl0gPSBudWxsO1xuICB9LCBvbkV4aXRpbmcpLCBbY29tcHV0ZWREaW1lbnNpb24sIG9uRXhpdGluZ10pO1xuICByZXR1cm4gLyojX19QVVJFX18qL19qc3goVHJhbnNpdGlvbldyYXBwZXIsIHtcbiAgICByZWY6IHJlZixcbiAgICBhZGRFbmRMaXN0ZW5lcjogdHJhbnNpdGlvbkVuZExpc3RlbmVyLFxuICAgIC4uLnByb3BzLFxuICAgIFwiYXJpYS1leHBhbmRlZFwiOiBwcm9wcy5yb2xlID8gcHJvcHMuaW4gOiBudWxsLFxuICAgIG9uRW50ZXI6IGhhbmRsZUVudGVyLFxuICAgIG9uRW50ZXJpbmc6IGhhbmRsZUVudGVyaW5nLFxuICAgIG9uRW50ZXJlZDogaGFuZGxlRW50ZXJlZCxcbiAgICBvbkV4aXQ6IGhhbmRsZUV4aXQsXG4gICAgb25FeGl0aW5nOiBoYW5kbGVFeGl0aW5nLFxuICAgIGNoaWxkUmVmOiBjaGlsZHJlbi5yZWYsXG4gICAgY2hpbGRyZW46IChzdGF0ZSwgaW5uZXJQcm9wcykgPT4gLyojX19QVVJFX18qL1JlYWN0LmNsb25lRWxlbWVudChjaGlsZHJlbiwge1xuICAgICAgLi4uaW5uZXJQcm9wcyxcbiAgICAgIGNsYXNzTmFtZTogY2xhc3NOYW1lcyhjbGFzc05hbWUsIGNoaWxkcmVuLnByb3BzLmNsYXNzTmFtZSwgY29sbGFwc2VTdHlsZXNbc3RhdGVdLCBjb21wdXRlZERpbWVuc2lvbiA9PT0gJ3dpZHRoJyAmJiAnY29sbGFwc2UtaG9yaXpvbnRhbCcpXG4gICAgfSlcbiAgfSk7XG59KTtcblxuLy8gQHRzLWlnbm9yZVxuXG4vLyBAdHMtaWdub3JlXG5Db2xsYXBzZS5kZWZhdWx0UHJvcHMgPSBkZWZhdWx0UHJvcHM7XG5leHBvcnQgZGVmYXVsdCBDb2xsYXBzZTsiLCJpbXBvcnQgKiBhcyBSZWFjdCBmcm9tICdyZWFjdCc7XG5leHBvcnQgZnVuY3Rpb24gaXNBY2NvcmRpb25JdGVtU2VsZWN0ZWQoYWN0aXZlRXZlbnRLZXksIGV2ZW50S2V5KSB7XG4gIHJldHVybiBBcnJheS5pc0FycmF5KGFjdGl2ZUV2ZW50S2V5KSA/IGFjdGl2ZUV2ZW50S2V5LmluY2x1ZGVzKGV2ZW50S2V5KSA6IGFjdGl2ZUV2ZW50S2V5ID09PSBldmVudEtleTtcbn1cbmNvbnN0IGNvbnRleHQgPSAvKiNfX1BVUkVfXyovUmVhY3QuY3JlYXRlQ29udGV4dCh7fSk7XG5jb250ZXh0LmRpc3BsYXlOYW1lID0gJ0FjY29yZGlvbkNvbnRleHQnO1xuZXhwb3J0IGRlZmF1bHQgY29udGV4dDsiLCJpbXBvcnQgY2xhc3NOYW1lcyBmcm9tICdjbGFzc25hbWVzJztcbmltcG9ydCAqIGFzIFJlYWN0IGZyb20gJ3JlYWN0JztcbmltcG9ydCB7IHVzZUNvbnRleHQgfSBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyB1c2VCb290c3RyYXBQcmVmaXggfSBmcm9tICcuL1RoZW1lUHJvdmlkZXInO1xuaW1wb3J0IENvbGxhcHNlIGZyb20gJy4vQ29sbGFwc2UnO1xuaW1wb3J0IEFjY29yZGlvbkNvbnRleHQsIHsgaXNBY2NvcmRpb25JdGVtU2VsZWN0ZWQgfSBmcm9tICcuL0FjY29yZGlvbkNvbnRleHQnO1xuaW1wb3J0IHsganN4IGFzIF9qc3ggfSBmcm9tIFwicmVhY3QvanN4LXJ1bnRpbWVcIjtcbi8qKlxuICogVGhpcyBjb21wb25lbnQgYWNjZXB0cyBhbGwgb2YgW2BDb2xsYXBzZWAncyBwcm9wc10oL3V0aWxpdGllcy90cmFuc2l0aW9ucy8jY29sbGFwc2UtcHJvcHMpLlxuICovXG5jb25zdCBBY2NvcmRpb25Db2xsYXBzZSA9IC8qI19fUFVSRV9fKi9SZWFjdC5mb3J3YXJkUmVmKCh7XG4gIGFzOiBDb21wb25lbnQgPSAnZGl2JyxcbiAgYnNQcmVmaXgsXG4gIGNsYXNzTmFtZSxcbiAgY2hpbGRyZW4sXG4gIGV2ZW50S2V5LFxuICAuLi5wcm9wc1xufSwgcmVmKSA9PiB7XG4gIGNvbnN0IHtcbiAgICBhY3RpdmVFdmVudEtleVxuICB9ID0gdXNlQ29udGV4dChBY2NvcmRpb25Db250ZXh0KTtcbiAgYnNQcmVmaXggPSB1c2VCb290c3RyYXBQcmVmaXgoYnNQcmVmaXgsICdhY2NvcmRpb24tY29sbGFwc2UnKTtcbiAgcmV0dXJuIC8qI19fUFVSRV9fKi9fanN4KENvbGxhcHNlLCB7XG4gICAgcmVmOiByZWYsXG4gICAgaW46IGlzQWNjb3JkaW9uSXRlbVNlbGVjdGVkKGFjdGl2ZUV2ZW50S2V5LCBldmVudEtleSksXG4gICAgLi4ucHJvcHMsXG4gICAgY2xhc3NOYW1lOiBjbGFzc05hbWVzKGNsYXNzTmFtZSwgYnNQcmVmaXgpLFxuICAgIGNoaWxkcmVuOiAvKiNfX1BVUkVfXyovX2pzeChDb21wb25lbnQsIHtcbiAgICAgIGNoaWxkcmVuOiBSZWFjdC5DaGlsZHJlbi5vbmx5KGNoaWxkcmVuKVxuICAgIH0pXG4gIH0pO1xufSk7XG5BY2NvcmRpb25Db2xsYXBzZS5kaXNwbGF5TmFtZSA9ICdBY2NvcmRpb25Db2xsYXBzZSc7XG5leHBvcnQgZGVmYXVsdCBBY2NvcmRpb25Db2xsYXBzZTsiLCJpbXBvcnQgKiBhcyBSZWFjdCBmcm9tICdyZWFjdCc7XG5jb25zdCBjb250ZXh0ID0gLyojX19QVVJFX18qL1JlYWN0LmNyZWF0ZUNvbnRleHQoe1xuICBldmVudEtleTogJydcbn0pO1xuY29udGV4dC5kaXNwbGF5TmFtZSA9ICdBY2NvcmRpb25JdGVtQ29udGV4dCc7XG5leHBvcnQgZGVmYXVsdCBjb250ZXh0OyIsImltcG9ydCBjbGFzc05hbWVzIGZyb20gJ2NsYXNzbmFtZXMnO1xuaW1wb3J0ICogYXMgUmVhY3QgZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsgdXNlQ29udGV4dCB9IGZyb20gJ3JlYWN0JztcbmltcG9ydCB7IHVzZUJvb3RzdHJhcFByZWZpeCB9IGZyb20gJy4vVGhlbWVQcm92aWRlcic7XG5pbXBvcnQgQWNjb3JkaW9uQ29sbGFwc2UgZnJvbSAnLi9BY2NvcmRpb25Db2xsYXBzZSc7XG5pbXBvcnQgQWNjb3JkaW9uSXRlbUNvbnRleHQgZnJvbSAnLi9BY2NvcmRpb25JdGVtQ29udGV4dCc7XG5pbXBvcnQgeyBqc3ggYXMgX2pzeCB9IGZyb20gXCJyZWFjdC9qc3gtcnVudGltZVwiO1xuY29uc3QgQWNjb3JkaW9uQm9keSA9IC8qI19fUFVSRV9fKi9SZWFjdC5mb3J3YXJkUmVmKCh7XG4gIC8vIE5lZWQgdG8gZGVmaW5lIHRoZSBkZWZhdWx0IFwiYXNcIiBkdXJpbmcgcHJvcCBkZXN0cnVjdHVyaW5nIHRvIGJlIGNvbXBhdGlibGUgd2l0aCBzdHlsZWQtY29tcG9uZW50cyBnaXRodWIuY29tL3JlYWN0LWJvb3RzdHJhcC9yZWFjdC1ib290c3RyYXAvaXNzdWVzLzM1OTVcbiAgYXM6IENvbXBvbmVudCA9ICdkaXYnLFxuICBic1ByZWZpeCxcbiAgY2xhc3NOYW1lLFxuICBvbkVudGVyLFxuICBvbkVudGVyaW5nLFxuICBvbkVudGVyZWQsXG4gIG9uRXhpdCxcbiAgb25FeGl0aW5nLFxuICBvbkV4aXRlZCxcbiAgLi4ucHJvcHNcbn0sIHJlZikgPT4ge1xuICBic1ByZWZpeCA9IHVzZUJvb3RzdHJhcFByZWZpeChic1ByZWZpeCwgJ2FjY29yZGlvbi1ib2R5Jyk7XG4gIGNvbnN0IHtcbiAgICBldmVudEtleVxuICB9ID0gdXNlQ29udGV4dChBY2NvcmRpb25JdGVtQ29udGV4dCk7XG4gIHJldHVybiAvKiNfX1BVUkVfXyovX2pzeChBY2NvcmRpb25Db2xsYXBzZSwge1xuICAgIGV2ZW50S2V5OiBldmVudEtleSxcbiAgICBvbkVudGVyOiBvbkVudGVyLFxuICAgIG9uRW50ZXJpbmc6IG9uRW50ZXJpbmcsXG4gICAgb25FbnRlcmVkOiBvbkVudGVyZWQsXG4gICAgb25FeGl0OiBvbkV4aXQsXG4gICAgb25FeGl0aW5nOiBvbkV4aXRpbmcsXG4gICAgb25FeGl0ZWQ6IG9uRXhpdGVkLFxuICAgIGNoaWxkcmVuOiAvKiNfX1BVUkVfXyovX2pzeChDb21wb25lbnQsIHtcbiAgICAgIHJlZjogcmVmLFxuICAgICAgLi4ucHJvcHMsXG4gICAgICBjbGFzc05hbWU6IGNsYXNzTmFtZXMoY2xhc3NOYW1lLCBic1ByZWZpeClcbiAgICB9KVxuICB9KTtcbn0pO1xuQWNjb3JkaW9uQm9keS5kaXNwbGF5TmFtZSA9ICdBY2NvcmRpb25Cb2R5JztcbmV4cG9ydCBkZWZhdWx0IEFjY29yZGlvbkJvZHk7IiwiaW1wb3J0ICogYXMgUmVhY3QgZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsgdXNlQ29udGV4dCB9IGZyb20gJ3JlYWN0JztcbmltcG9ydCBjbGFzc05hbWVzIGZyb20gJ2NsYXNzbmFtZXMnO1xuaW1wb3J0IEFjY29yZGlvbkNvbnRleHQsIHsgaXNBY2NvcmRpb25JdGVtU2VsZWN0ZWQgfSBmcm9tICcuL0FjY29yZGlvbkNvbnRleHQnO1xuaW1wb3J0IEFjY29yZGlvbkl0ZW1Db250ZXh0IGZyb20gJy4vQWNjb3JkaW9uSXRlbUNvbnRleHQnO1xuaW1wb3J0IHsgdXNlQm9vdHN0cmFwUHJlZml4IH0gZnJvbSAnLi9UaGVtZVByb3ZpZGVyJztcbmltcG9ydCB7IGpzeCBhcyBfanN4IH0gZnJvbSBcInJlYWN0L2pzeC1ydW50aW1lXCI7XG5leHBvcnQgZnVuY3Rpb24gdXNlQWNjb3JkaW9uQnV0dG9uKGV2ZW50S2V5LCBvbkNsaWNrKSB7XG4gIGNvbnN0IHtcbiAgICBhY3RpdmVFdmVudEtleSxcbiAgICBvblNlbGVjdCxcbiAgICBhbHdheXNPcGVuXG4gIH0gPSB1c2VDb250ZXh0KEFjY29yZGlvbkNvbnRleHQpO1xuICByZXR1cm4gZSA9PiB7XG4gICAgLypcbiAgICAgIENvbXBhcmUgdGhlIGV2ZW50IGtleSBpbiBjb250ZXh0IHdpdGggdGhlIGdpdmVuIGV2ZW50IGtleS5cbiAgICAgIElmIHRoZXkgYXJlIHRoZSBzYW1lLCB0aGVuIGNvbGxhcHNlIHRoZSBjb21wb25lbnQuXG4gICAgKi9cbiAgICBsZXQgZXZlbnRLZXlQYXNzZWQgPSBldmVudEtleSA9PT0gYWN0aXZlRXZlbnRLZXkgPyBudWxsIDogZXZlbnRLZXk7XG4gICAgaWYgKGFsd2F5c09wZW4pIHtcbiAgICAgIGlmIChBcnJheS5pc0FycmF5KGFjdGl2ZUV2ZW50S2V5KSkge1xuICAgICAgICBpZiAoYWN0aXZlRXZlbnRLZXkuaW5jbHVkZXMoZXZlbnRLZXkpKSB7XG4gICAgICAgICAgZXZlbnRLZXlQYXNzZWQgPSBhY3RpdmVFdmVudEtleS5maWx0ZXIoayA9PiBrICE9PSBldmVudEtleSk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgZXZlbnRLZXlQYXNzZWQgPSBbLi4uYWN0aXZlRXZlbnRLZXksIGV2ZW50S2V5XTtcbiAgICAgICAgfVxuICAgICAgfSBlbHNlIHtcbiAgICAgICAgLy8gYWN0aXZlRXZlbnRLZXkgaXMgdW5kZWZpbmVkLlxuICAgICAgICBldmVudEtleVBhc3NlZCA9IFtldmVudEtleV07XG4gICAgICB9XG4gICAgfVxuICAgIG9uU2VsZWN0ID09IG51bGwgPyB2b2lkIDAgOiBvblNlbGVjdChldmVudEtleVBhc3NlZCwgZSk7XG4gICAgb25DbGljayA9PSBudWxsID8gdm9pZCAwIDogb25DbGljayhlKTtcbiAgfTtcbn1cbmNvbnN0IEFjY29yZGlvbkJ1dHRvbiA9IC8qI19fUFVSRV9fKi9SZWFjdC5mb3J3YXJkUmVmKCh7XG4gIC8vIE5lZWQgdG8gZGVmaW5lIHRoZSBkZWZhdWx0IFwiYXNcIiBkdXJpbmcgcHJvcCBkZXN0cnVjdHVyaW5nIHRvIGJlIGNvbXBhdGlibGUgd2l0aCBzdHlsZWQtY29tcG9uZW50cyBnaXRodWIuY29tL3JlYWN0LWJvb3RzdHJhcC9yZWFjdC1ib290c3RyYXAvaXNzdWVzLzM1OTVcbiAgYXM6IENvbXBvbmVudCA9ICdidXR0b24nLFxuICBic1ByZWZpeCxcbiAgY2xhc3NOYW1lLFxuICBvbkNsaWNrLFxuICAuLi5wcm9wc1xufSwgcmVmKSA9PiB7XG4gIGJzUHJlZml4ID0gdXNlQm9vdHN0cmFwUHJlZml4KGJzUHJlZml4LCAnYWNjb3JkaW9uLWJ1dHRvbicpO1xuICBjb25zdCB7XG4gICAgZXZlbnRLZXlcbiAgfSA9IHVzZUNvbnRleHQoQWNjb3JkaW9uSXRlbUNvbnRleHQpO1xuICBjb25zdCBhY2NvcmRpb25PbkNsaWNrID0gdXNlQWNjb3JkaW9uQnV0dG9uKGV2ZW50S2V5LCBvbkNsaWNrKTtcbiAgY29uc3Qge1xuICAgIGFjdGl2ZUV2ZW50S2V5XG4gIH0gPSB1c2VDb250ZXh0KEFjY29yZGlvbkNvbnRleHQpO1xuICBpZiAoQ29tcG9uZW50ID09PSAnYnV0dG9uJykge1xuICAgIHByb3BzLnR5cGUgPSAnYnV0dG9uJztcbiAgfVxuICByZXR1cm4gLyojX19QVVJFX18qL19qc3goQ29tcG9uZW50LCB7XG4gICAgcmVmOiByZWYsXG4gICAgb25DbGljazogYWNjb3JkaW9uT25DbGljayxcbiAgICAuLi5wcm9wcyxcbiAgICBcImFyaWEtZXhwYW5kZWRcIjogZXZlbnRLZXkgPT09IGFjdGl2ZUV2ZW50S2V5LFxuICAgIGNsYXNzTmFtZTogY2xhc3NOYW1lcyhjbGFzc05hbWUsIGJzUHJlZml4LCAhaXNBY2NvcmRpb25JdGVtU2VsZWN0ZWQoYWN0aXZlRXZlbnRLZXksIGV2ZW50S2V5KSAmJiAnY29sbGFwc2VkJylcbiAgfSk7XG59KTtcbkFjY29yZGlvbkJ1dHRvbi5kaXNwbGF5TmFtZSA9ICdBY2NvcmRpb25CdXR0b24nO1xuZXhwb3J0IGRlZmF1bHQgQWNjb3JkaW9uQnV0dG9uOyIsImltcG9ydCBjbGFzc05hbWVzIGZyb20gJ2NsYXNzbmFtZXMnO1xuaW1wb3J0ICogYXMgUmVhY3QgZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsgdXNlQm9vdHN0cmFwUHJlZml4IH0gZnJvbSAnLi9UaGVtZVByb3ZpZGVyJztcbmltcG9ydCBBY2NvcmRpb25CdXR0b24gZnJvbSAnLi9BY2NvcmRpb25CdXR0b24nO1xuaW1wb3J0IHsganN4IGFzIF9qc3ggfSBmcm9tIFwicmVhY3QvanN4LXJ1bnRpbWVcIjtcbmNvbnN0IEFjY29yZGlvbkhlYWRlciA9IC8qI19fUFVSRV9fKi9SZWFjdC5mb3J3YXJkUmVmKCh7XG4gIC8vIE5lZWQgdG8gZGVmaW5lIHRoZSBkZWZhdWx0IFwiYXNcIiBkdXJpbmcgcHJvcCBkZXN0cnVjdHVyaW5nIHRvIGJlIGNvbXBhdGlibGUgd2l0aCBzdHlsZWQtY29tcG9uZW50cyBnaXRodWIuY29tL3JlYWN0LWJvb3RzdHJhcC9yZWFjdC1ib290c3RyYXAvaXNzdWVzLzM1OTVcbiAgYXM6IENvbXBvbmVudCA9ICdoMicsXG4gIGJzUHJlZml4LFxuICBjbGFzc05hbWUsXG4gIGNoaWxkcmVuLFxuICBvbkNsaWNrLFxuICAuLi5wcm9wc1xufSwgcmVmKSA9PiB7XG4gIGJzUHJlZml4ID0gdXNlQm9vdHN0cmFwUHJlZml4KGJzUHJlZml4LCAnYWNjb3JkaW9uLWhlYWRlcicpO1xuICByZXR1cm4gLyojX19QVVJFX18qL19qc3goQ29tcG9uZW50LCB7XG4gICAgcmVmOiByZWYsXG4gICAgLi4ucHJvcHMsXG4gICAgY2xhc3NOYW1lOiBjbGFzc05hbWVzKGNsYXNzTmFtZSwgYnNQcmVmaXgpLFxuICAgIGNoaWxkcmVuOiAvKiNfX1BVUkVfXyovX2pzeChBY2NvcmRpb25CdXR0b24sIHtcbiAgICAgIG9uQ2xpY2s6IG9uQ2xpY2ssXG4gICAgICBjaGlsZHJlbjogY2hpbGRyZW5cbiAgICB9KVxuICB9KTtcbn0pO1xuQWNjb3JkaW9uSGVhZGVyLmRpc3BsYXlOYW1lID0gJ0FjY29yZGlvbkhlYWRlcic7XG5leHBvcnQgZGVmYXVsdCBBY2NvcmRpb25IZWFkZXI7IiwiaW1wb3J0IGNsYXNzTmFtZXMgZnJvbSAnY2xhc3NuYW1lcyc7XG5pbXBvcnQgKiBhcyBSZWFjdCBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyB1c2VNZW1vIH0gZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsgdXNlQm9vdHN0cmFwUHJlZml4IH0gZnJvbSAnLi9UaGVtZVByb3ZpZGVyJztcbmltcG9ydCBBY2NvcmRpb25JdGVtQ29udGV4dCBmcm9tICcuL0FjY29yZGlvbkl0ZW1Db250ZXh0JztcbmltcG9ydCB7IGpzeCBhcyBfanN4IH0gZnJvbSBcInJlYWN0L2pzeC1ydW50aW1lXCI7XG5jb25zdCBBY2NvcmRpb25JdGVtID0gLyojX19QVVJFX18qL1JlYWN0LmZvcndhcmRSZWYoKHtcbiAgLy8gTmVlZCB0byBkZWZpbmUgdGhlIGRlZmF1bHQgXCJhc1wiIGR1cmluZyBwcm9wIGRlc3RydWN0dXJpbmcgdG8gYmUgY29tcGF0aWJsZSB3aXRoIHN0eWxlZC1jb21wb25lbnRzIGdpdGh1Yi5jb20vcmVhY3QtYm9vdHN0cmFwL3JlYWN0LWJvb3RzdHJhcC9pc3N1ZXMvMzU5NVxuICBhczogQ29tcG9uZW50ID0gJ2RpdicsXG4gIGJzUHJlZml4LFxuICBjbGFzc05hbWUsXG4gIGV2ZW50S2V5LFxuICAuLi5wcm9wc1xufSwgcmVmKSA9PiB7XG4gIGJzUHJlZml4ID0gdXNlQm9vdHN0cmFwUHJlZml4KGJzUHJlZml4LCAnYWNjb3JkaW9uLWl0ZW0nKTtcbiAgY29uc3QgY29udGV4dFZhbHVlID0gdXNlTWVtbygoKSA9PiAoe1xuICAgIGV2ZW50S2V5XG4gIH0pLCBbZXZlbnRLZXldKTtcbiAgcmV0dXJuIC8qI19fUFVSRV9fKi9fanN4KEFjY29yZGlvbkl0ZW1Db250ZXh0LlByb3ZpZGVyLCB7XG4gICAgdmFsdWU6IGNvbnRleHRWYWx1ZSxcbiAgICBjaGlsZHJlbjogLyojX19QVVJFX18qL19qc3goQ29tcG9uZW50LCB7XG4gICAgICByZWY6IHJlZixcbiAgICAgIC4uLnByb3BzLFxuICAgICAgY2xhc3NOYW1lOiBjbGFzc05hbWVzKGNsYXNzTmFtZSwgYnNQcmVmaXgpXG4gICAgfSlcbiAgfSk7XG59KTtcbkFjY29yZGlvbkl0ZW0uZGlzcGxheU5hbWUgPSAnQWNjb3JkaW9uSXRlbSc7XG5leHBvcnQgZGVmYXVsdCBBY2NvcmRpb25JdGVtOyIsImltcG9ydCBjbGFzc05hbWVzIGZyb20gJ2NsYXNzbmFtZXMnO1xuaW1wb3J0ICogYXMgUmVhY3QgZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsgdXNlTWVtbyB9IGZyb20gJ3JlYWN0JztcbmltcG9ydCB7IHVzZVVuY29udHJvbGxlZCB9IGZyb20gJ3VuY29udHJvbGxhYmxlJztcbmltcG9ydCB7IHVzZUJvb3RzdHJhcFByZWZpeCB9IGZyb20gJy4vVGhlbWVQcm92aWRlcic7XG5pbXBvcnQgQWNjb3JkaW9uQm9keSBmcm9tICcuL0FjY29yZGlvbkJvZHknO1xuaW1wb3J0IEFjY29yZGlvbkJ1dHRvbiBmcm9tICcuL0FjY29yZGlvbkJ1dHRvbic7XG5pbXBvcnQgQWNjb3JkaW9uQ29sbGFwc2UgZnJvbSAnLi9BY2NvcmRpb25Db2xsYXBzZSc7XG5pbXBvcnQgQWNjb3JkaW9uQ29udGV4dCBmcm9tICcuL0FjY29yZGlvbkNvbnRleHQnO1xuaW1wb3J0IEFjY29yZGlvbkhlYWRlciBmcm9tICcuL0FjY29yZGlvbkhlYWRlcic7XG5pbXBvcnQgQWNjb3JkaW9uSXRlbSBmcm9tICcuL0FjY29yZGlvbkl0ZW0nO1xuaW1wb3J0IHsganN4IGFzIF9qc3ggfSBmcm9tIFwicmVhY3QvanN4LXJ1bnRpbWVcIjtcbmNvbnN0IEFjY29yZGlvbiA9IC8qI19fUFVSRV9fKi9SZWFjdC5mb3J3YXJkUmVmKChwcm9wcywgcmVmKSA9PiB7XG4gIGNvbnN0IHtcbiAgICAvLyBOZWVkIHRvIGRlZmluZSB0aGUgZGVmYXVsdCBcImFzXCIgZHVyaW5nIHByb3AgZGVzdHJ1Y3R1cmluZyB0byBiZSBjb21wYXRpYmxlIHdpdGggc3R5bGVkLWNvbXBvbmVudHMgZ2l0aHViLmNvbS9yZWFjdC1ib290c3RyYXAvcmVhY3QtYm9vdHN0cmFwL2lzc3Vlcy8zNTk1XG4gICAgYXM6IENvbXBvbmVudCA9ICdkaXYnLFxuICAgIGFjdGl2ZUtleSxcbiAgICBic1ByZWZpeCxcbiAgICBjbGFzc05hbWUsXG4gICAgb25TZWxlY3QsXG4gICAgZmx1c2gsXG4gICAgYWx3YXlzT3BlbixcbiAgICAuLi5jb250cm9sbGVkUHJvcHNcbiAgfSA9IHVzZVVuY29udHJvbGxlZChwcm9wcywge1xuICAgIGFjdGl2ZUtleTogJ29uU2VsZWN0J1xuICB9KTtcbiAgY29uc3QgcHJlZml4ID0gdXNlQm9vdHN0cmFwUHJlZml4KGJzUHJlZml4LCAnYWNjb3JkaW9uJyk7XG4gIGNvbnN0IGNvbnRleHRWYWx1ZSA9IHVzZU1lbW8oKCkgPT4gKHtcbiAgICBhY3RpdmVFdmVudEtleTogYWN0aXZlS2V5LFxuICAgIG9uU2VsZWN0LFxuICAgIGFsd2F5c09wZW5cbiAgfSksIFthY3RpdmVLZXksIG9uU2VsZWN0LCBhbHdheXNPcGVuXSk7XG4gIHJldHVybiAvKiNfX1BVUkVfXyovX2pzeChBY2NvcmRpb25Db250ZXh0LlByb3ZpZGVyLCB7XG4gICAgdmFsdWU6IGNvbnRleHRWYWx1ZSxcbiAgICBjaGlsZHJlbjogLyojX19QVVJFX18qL19qc3goQ29tcG9uZW50LCB7XG4gICAgICByZWY6IHJlZixcbiAgICAgIC4uLmNvbnRyb2xsZWRQcm9wcyxcbiAgICAgIGNsYXNzTmFtZTogY2xhc3NOYW1lcyhjbGFzc05hbWUsIHByZWZpeCwgZmx1c2ggJiYgYCR7cHJlZml4fS1mbHVzaGApXG4gICAgfSlcbiAgfSk7XG59KTtcbkFjY29yZGlvbi5kaXNwbGF5TmFtZSA9ICdBY2NvcmRpb24nO1xuZXhwb3J0IGRlZmF1bHQgT2JqZWN0LmFzc2lnbihBY2NvcmRpb24sIHtcbiAgQnV0dG9uOiBBY2NvcmRpb25CdXR0b24sXG4gIENvbGxhcHNlOiBBY2NvcmRpb25Db2xsYXBzZSxcbiAgSXRlbTogQWNjb3JkaW9uSXRlbSxcbiAgSGVhZGVyOiBBY2NvcmRpb25IZWFkZXIsXG4gIEJvZHk6IEFjY29yZGlvbkJvZHlcbn0pOyIsImltcG9ydCB7IENvbXBvbmVudCwgUmVhY3ROb2RlLCBjcmVhdGVFbGVtZW50IH0gZnJvbSBcInJlYWN0XCI7XG5cbmltcG9ydCB7IEFjY29yZGlhbkNvbnRhaW5lclByb3BzIH0gZnJvbSBcIi4uL3R5cGluZ3MvQWNjb3JkaWFuUHJvcHNcIjtcblxuaW1wb3J0IFwiLi91aS9BY2NvcmRpYW4uY3NzXCI7XG5cbmltcG9ydCBBY2NvcmRpb24gZnJvbSBcInJlYWN0LWJvb3RzdHJhcC9BY2NvcmRpb25cIjtcblxuZXhwb3J0IGNsYXNzIEFjY29yZGlhbiBleHRlbmRzIENvbXBvbmVudDxBY2NvcmRpYW5Db250YWluZXJQcm9wcz4ge1xuXG4gICAgcHVibGljIGhlYWRlciA9IHRoaXMucHJvcHMuaGVhZGluZz8udmFsdWUgPyB0aGlzLnByb3BzLmhlYWRpbmc/LnZhbHVlIDogXCIgXCI7XG4gIFxuXG4gICAgaGFuZGxlRW50ZXIgPSAoKT0+e1xuICAgICAgICBpZiAodGhpcy5wcm9wcy5vbkVudGVyICYmIHRoaXMucHJvcHMub25FbnRlci5jYW5FeGVjdXRlKSB7XG4gICAgICAgICAgICB0aGlzLnByb3BzLm9uRW50ZXIuZXhlY3V0ZSgpO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgaGFuZGxlRXhpdCA9ICgpPT57XG4gICAgICAgIGlmICh0aGlzLnByb3BzLm9uRXhpdCAmJiB0aGlzLnByb3BzLm9uRXhpdC5jYW5FeGVjdXRlKSB7XG4gICAgICAgICAgICB0aGlzLnByb3BzLm9uRXhpdC5leGVjdXRlKCk7XG4gICAgICAgIH1cbiAgICB9XG5cbiAgICBoYW5kbGVyID0gKCk9PntcbiAgICAgICAgaWYodGhpcy5wcm9wcy5ib29sZWFuKXtcbiAgICAgICAgICAgIGlmICh0aGlzLnByb3BzLm9uRW50ZXIgJiYgdGhpcy5wcm9wcy5vbkVudGVyLmNhbkV4ZWN1dGUpIHtcbiAgICAgICAgICAgICAgICB0aGlzLnByb3BzLm9uRW50ZXIuZXhlY3V0ZSgpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIFwiMFwiO1xuICAgICAgICB9ZWxzZXtcbiAgICAgICAgICAgIHJldHVybiBcIlwiO1xuICAgICAgICB9XG4gICAgfVxuXG4gICAgaGFuZGxlZGVmYXVsdG9wZW4gOiBhbnkgPSAgdGhpcy5oYW5kbGVyO1xuXG4gICAgcmVuZGVyKCk6IFJlYWN0Tm9kZSB7XG4gICAgICAgIHRoaXMuaGVhZGVyID0gdGhpcy5wcm9wcy5oZWFkaW5nPy52YWx1ZSA/IHRoaXMucHJvcHMuaGVhZGluZz8udmFsdWUgOiBcIiBcIjtcblxuICAgICAgICByZXR1cm4gKFxuICAgICAgICAgICAgICAgIDxBY2NvcmRpb24gZGVmYXVsdEFjdGl2ZUtleT17dGhpcy5oYW5kbGVkZWZhdWx0b3Blbn0+XG4gICAgICAgICAgICAgICAgICAgIDxBY2NvcmRpb24uSXRlbSBldmVudEtleT1cIjBcIj5cbiAgICAgICAgICAgICAgICAgICAgICAgIDxBY2NvcmRpb24uSGVhZGVyIGNsYXNzTmFtZT1cIkFjY29yZGlhbkhlYWRlclwiPnt0aGlzLmhlYWRlcn08L0FjY29yZGlvbi5IZWFkZXI+XG4gICAgICAgICAgICAgICAgICAgICAgICA8QWNjb3JkaW9uLkJvZHkgb25FbnRlcj17dGhpcy5oYW5kbGVFbnRlcn0gb25FeGl0PXt0aGlzLmhhbmRsZUV4aXR9PlxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHt0aGlzLnByb3BzLmNvbnRlbnR9XG4gICAgICAgICAgICAgICAgICAgICAgICA8L0FjY29yZGlvbi5Cb2R5PlxuICAgICAgICAgICAgICAgICAgICA8L0FjY29yZGlvbi5JdGVtPlxuICAgICAgICAgICAgICAgIDwvQWNjb3JkaW9uPlxuICAgICAgICApO1xuICAgIH1cbn1cbiJdLCJuYW1lcyI6WyJoYXNPd24iLCJoYXNPd25Qcm9wZXJ0eSIsImNsYXNzTmFtZXMiLCJjbGFzc2VzIiwiaSIsImFyZ3VtZW50cyIsImxlbmd0aCIsImFyZyIsImFyZ1R5cGUiLCJwdXNoIiwiQXJyYXkiLCJpc0FycmF5IiwiaW5uZXIiLCJhcHBseSIsInRvU3RyaW5nIiwiT2JqZWN0IiwicHJvdG90eXBlIiwiaW5jbHVkZXMiLCJrZXkiLCJjYWxsIiwiam9pbiIsIm1vZHVsZSIsImV4cG9ydHMiLCJkZWZhdWx0Iiwid2luZG93IiwiX2V4dGVuZHMiLCJhc3NpZ24iLCJiaW5kIiwidGFyZ2V0Iiwic291cmNlIiwiX29iamVjdFdpdGhvdXRQcm9wZXJ0aWVzTG9vc2UiLCJleGNsdWRlZCIsInNvdXJjZUtleXMiLCJrZXlzIiwiaW5kZXhPZiIsImRlZmF1bHRLZXkiLCJjaGFyQXQiLCJ0b1VwcGVyQ2FzZSIsInN1YnN0ciIsIl90b1Byb3BlcnR5S2V5IiwiX3RvUHJpbWl0aXZlIiwiU3RyaW5nIiwiaW5wdXQiLCJoaW50IiwicHJpbSIsIlN5bWJvbCIsInRvUHJpbWl0aXZlIiwidW5kZWZpbmVkIiwicmVzIiwiVHlwZUVycm9yIiwiTnVtYmVyIiwidXNlVW5jb250cm9sbGVkUHJvcCIsInByb3BWYWx1ZSIsImRlZmF1bHRWYWx1ZSIsImhhbmRsZXIiLCJ3YXNQcm9wUmVmIiwidXNlUmVmIiwiX3VzZVN0YXRlIiwidXNlU3RhdGUiLCJzdGF0ZVZhbHVlIiwic2V0U3RhdGUiLCJpc1Byb3AiLCJ3YXNQcm9wIiwiY3VycmVudCIsInVzZUNhbGxiYWNrIiwidmFsdWUiLCJfbGVuIiwiYXJncyIsIl9rZXkiLCJjb25jYXQiLCJ1c2VVbmNvbnRyb2xsZWQiLCJwcm9wcyIsImNvbmZpZyIsInJlZHVjZSIsInJlc3VsdCIsImZpZWxkTmFtZSIsIl9leHRlbmRzMiIsIl9yZWYiLCJVdGlscyIsInByb3BzVmFsdWUiLCJyZXN0IiwibWFwIiwiaGFuZGxlck5hbWUiLCJfdXNlVW5jb250cm9sbGVkUHJvcCIsIl9zZXRQcm90b3R5cGVPZiIsIm8iLCJwIiwic2V0UHJvdG90eXBlT2YiLCJfX3Byb3RvX18iLCJfaW5oZXJpdHNMb29zZSIsInN1YkNsYXNzIiwic3VwZXJDbGFzcyIsImNyZWF0ZSIsImNvbnN0cnVjdG9yIiwiREVGQVVMVF9CUkVBS1BPSU5UUyIsIkRFRkFVTFRfTUlOX0JSRUFLUE9JTlQiLCJUaGVtZUNvbnRleHQiLCJSZWFjdCIsImNyZWF0ZUNvbnRleHQiLCJwcmVmaXhlcyIsImJyZWFrcG9pbnRzIiwibWluQnJlYWtwb2ludCIsInVzZUJvb3RzdHJhcFByZWZpeCIsInByZWZpeCIsImRlZmF1bHRQcmVmaXgiLCJ1c2VDb250ZXh0Iiwib3duZXJEb2N1bWVudCIsIm5vZGUiLCJkb2N1bWVudCIsIm93bmVyV2luZG93IiwiZG9jIiwiZGVmYXVsdFZpZXciLCJnZXRDb21wdXRlZFN0eWxlIiwicHN1ZWRvRWxlbWVudCIsInJVcHBlciIsImh5cGhlbmF0ZSIsInN0cmluZyIsInJlcGxhY2UiLCJ0b0xvd2VyQ2FzZSIsIm1zUGF0dGVybiIsImh5cGhlbmF0ZVN0eWxlTmFtZSIsInN1cHBvcnRlZFRyYW5zZm9ybXMiLCJpc1RyYW5zZm9ybSIsInRlc3QiLCJzdHlsZSIsInByb3BlcnR5IiwiY3NzIiwidHJhbnNmb3JtcyIsImdldFByb3BlcnR5VmFsdWUiLCJmb3JFYWNoIiwicmVtb3ZlUHJvcGVydHkiLCJjc3NUZXh0IiwiaGFzU3ltYm9sIiwiZm9yIiwiUkVBQ1RfRUxFTUVOVF9UWVBFIiwiUkVBQ1RfUE9SVEFMX1RZUEUiLCJSRUFDVF9GUkFHTUVOVF9UWVBFIiwiUkVBQ1RfU1RSSUNUX01PREVfVFlQRSIsIlJFQUNUX1BST0ZJTEVSX1RZUEUiLCJSRUFDVF9QUk9WSURFUl9UWVBFIiwiUkVBQ1RfQ09OVEVYVF9UWVBFIiwiUkVBQ1RfQVNZTkNfTU9ERV9UWVBFIiwiUkVBQ1RfQ09OQ1VSUkVOVF9NT0RFX1RZUEUiLCJSRUFDVF9GT1JXQVJEX1JFRl9UWVBFIiwiUkVBQ1RfU1VTUEVOU0VfVFlQRSIsIlJFQUNUX1NVU1BFTlNFX0xJU1RfVFlQRSIsIlJFQUNUX01FTU9fVFlQRSIsIlJFQUNUX0xBWllfVFlQRSIsIlJFQUNUX0JMT0NLX1RZUEUiLCJSRUFDVF9GVU5EQU1FTlRBTF9UWVBFIiwiUkVBQ1RfUkVTUE9OREVSX1RZUEUiLCJSRUFDVF9TQ09QRV9UWVBFIiwiaXNWYWxpZEVsZW1lbnRUeXBlIiwidHlwZSIsIiQkdHlwZW9mIiwidHlwZU9mIiwib2JqZWN0IiwiJCR0eXBlb2ZUeXBlIiwiQXN5bmNNb2RlIiwiQ29uY3VycmVudE1vZGUiLCJDb250ZXh0Q29uc3VtZXIiLCJDb250ZXh0UHJvdmlkZXIiLCJFbGVtZW50IiwiRm9yd2FyZFJlZiIsIkZyYWdtZW50IiwiTGF6eSIsIk1lbW8iLCJQb3J0YWwiLCJQcm9maWxlciIsIlN0cmljdE1vZGUiLCJTdXNwZW5zZSIsImhhc1dhcm5lZEFib3V0RGVwcmVjYXRlZElzQXN5bmNNb2RlIiwiaXNBc3luY01vZGUiLCJjb25zb2xlIiwiaXNDb25jdXJyZW50TW9kZSIsImlzQ29udGV4dENvbnN1bWVyIiwiaXNDb250ZXh0UHJvdmlkZXIiLCJpc0VsZW1lbnQiLCJpc0ZvcndhcmRSZWYiLCJpc0ZyYWdtZW50IiwiaXNMYXp5IiwiaXNNZW1vIiwiaXNQb3J0YWwiLCJpc1Byb2ZpbGVyIiwiaXNTdHJpY3RNb2RlIiwiaXNTdXNwZW5zZSIsInJlcXVpcmUiLCJnZXRPd25Qcm9wZXJ0eVN5bWJvbHMiLCJwcm9wSXNFbnVtZXJhYmxlIiwicHJvcGVydHlJc0VudW1lcmFibGUiLCJ0b09iamVjdCIsInZhbCIsInNob3VsZFVzZU5hdGl2ZSIsInRlc3QxIiwiZ2V0T3duUHJvcGVydHlOYW1lcyIsInRlc3QyIiwiZnJvbUNoYXJDb2RlIiwib3JkZXIyIiwibiIsInRlc3QzIiwic3BsaXQiLCJsZXR0ZXIiLCJlcnIiLCJmcm9tIiwidG8iLCJzeW1ib2xzIiwicyIsIlJlYWN0UHJvcFR5cGVzU2VjcmV0IiwiRnVuY3Rpb24iLCJwcmludFdhcm5pbmciLCJsb2dnZWRUeXBlRmFpbHVyZXMiLCJoYXMiLCJ0ZXh0IiwibWVzc2FnZSIsImVycm9yIiwiRXJyb3IiLCJ4IiwiY2hlY2tQcm9wVHlwZXMiLCJ0eXBlU3BlY3MiLCJ2YWx1ZXMiLCJsb2NhdGlvbiIsImNvbXBvbmVudE5hbWUiLCJnZXRTdGFjayIsInR5cGVTcGVjTmFtZSIsIm5hbWUiLCJleCIsInN0YWNrIiwicmVzZXRXYXJuaW5nQ2FjaGUiLCJSZWFjdElzIiwiZW1wdHlGdW5jdGlvblRoYXRSZXR1cm5zTnVsbCIsImlzVmFsaWRFbGVtZW50IiwidGhyb3dPbkRpcmVjdEFjY2VzcyIsIklURVJBVE9SX1NZTUJPTCIsIml0ZXJhdG9yIiwiRkFVWF9JVEVSQVRPUl9TWU1CT0wiLCJnZXRJdGVyYXRvckZuIiwibWF5YmVJdGVyYWJsZSIsIml0ZXJhdG9yRm4iLCJBTk9OWU1PVVMiLCJSZWFjdFByb3BUeXBlcyIsImFycmF5IiwiY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIiLCJiaWdpbnQiLCJib29sIiwiZnVuYyIsIm51bWJlciIsInN5bWJvbCIsImFueSIsImNyZWF0ZUFueVR5cGVDaGVja2VyIiwiYXJyYXlPZiIsImNyZWF0ZUFycmF5T2ZUeXBlQ2hlY2tlciIsImVsZW1lbnQiLCJjcmVhdGVFbGVtZW50VHlwZUNoZWNrZXIiLCJlbGVtZW50VHlwZSIsImNyZWF0ZUVsZW1lbnRUeXBlVHlwZUNoZWNrZXIiLCJpbnN0YW5jZU9mIiwiY3JlYXRlSW5zdGFuY2VUeXBlQ2hlY2tlciIsImNyZWF0ZU5vZGVDaGVja2VyIiwib2JqZWN0T2YiLCJjcmVhdGVPYmplY3RPZlR5cGVDaGVja2VyIiwib25lT2YiLCJjcmVhdGVFbnVtVHlwZUNoZWNrZXIiLCJvbmVPZlR5cGUiLCJjcmVhdGVVbmlvblR5cGVDaGVja2VyIiwic2hhcGUiLCJjcmVhdGVTaGFwZVR5cGVDaGVja2VyIiwiZXhhY3QiLCJjcmVhdGVTdHJpY3RTaGFwZVR5cGVDaGVja2VyIiwiaXMiLCJ5IiwiUHJvcFR5cGVFcnJvciIsImRhdGEiLCJjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlciIsInZhbGlkYXRlIiwibWFudWFsUHJvcFR5cGVDYWxsQ2FjaGUiLCJtYW51YWxQcm9wVHlwZVdhcm5pbmdDb3VudCIsImNoZWNrVHlwZSIsImlzUmVxdWlyZWQiLCJwcm9wTmFtZSIsInByb3BGdWxsTmFtZSIsInNlY3JldCIsImNhY2hlS2V5IiwiY2hhaW5lZENoZWNrVHlwZSIsImV4cGVjdGVkVHlwZSIsInByb3BUeXBlIiwiZ2V0UHJvcFR5cGUiLCJwcmVjaXNlVHlwZSIsImdldFByZWNpc2VUeXBlIiwidHlwZUNoZWNrZXIiLCJleHBlY3RlZENsYXNzIiwiZXhwZWN0ZWRDbGFzc05hbWUiLCJhY3R1YWxDbGFzc05hbWUiLCJnZXRDbGFzc05hbWUiLCJleHBlY3RlZFZhbHVlcyIsInZhbHVlc1N0cmluZyIsIkpTT04iLCJzdHJpbmdpZnkiLCJyZXBsYWNlciIsImFycmF5T2ZUeXBlQ2hlY2tlcnMiLCJwcm9jZXNzIiwiY2hlY2tlciIsImdldFBvc3RmaXhGb3JUeXBlV2FybmluZyIsImV4cGVjdGVkVHlwZXMiLCJjaGVja2VyUmVzdWx0IiwiZXhwZWN0ZWRUeXBlc01lc3NhZ2UiLCJpc05vZGUiLCJpbnZhbGlkVmFsaWRhdG9yRXJyb3IiLCJzaGFwZVR5cGVzIiwiYWxsS2V5cyIsImV2ZXJ5Iiwic3RlcCIsImVudHJpZXMiLCJuZXh0IiwiZG9uZSIsImVudHJ5IiwiaXNTeW1ib2wiLCJSZWdFeHAiLCJEYXRlIiwiUHJvcFR5cGVzIiwiZGlzYWJsZWQiLCJ0aW1lb3V0c1NoYXBlIiwiZW50ZXIiLCJleGl0IiwiYXBwZWFyIiwiYWN0aXZlIiwiZW50ZXJEb25lIiwiZW50ZXJBY3RpdmUiLCJleGl0RG9uZSIsImV4aXRBY3RpdmUiLCJmb3JjZVJlZmxvdyIsInNjcm9sbFRvcCIsIlVOTU9VTlRFRCIsIkVYSVRFRCIsIkVOVEVSSU5HIiwiRU5URVJFRCIsIkVYSVRJTkciLCJUcmFuc2l0aW9uIiwiX1JlYWN0JENvbXBvbmVudCIsImNvbnRleHQiLCJfdGhpcyIsInBhcmVudEdyb3VwIiwiaXNNb3VudGluZyIsImluaXRpYWxTdGF0dXMiLCJhcHBlYXJTdGF0dXMiLCJpbiIsInVubW91bnRPbkV4aXQiLCJtb3VudE9uRW50ZXIiLCJzdGF0ZSIsInN0YXR1cyIsIm5leHRDYWxsYmFjayIsImdldERlcml2ZWRTdGF0ZUZyb21Qcm9wcyIsInByZXZTdGF0ZSIsIm5leHRJbiIsIl9wcm90byIsImNvbXBvbmVudERpZE1vdW50IiwidXBkYXRlU3RhdHVzIiwiY29tcG9uZW50RGlkVXBkYXRlIiwicHJldlByb3BzIiwibmV4dFN0YXR1cyIsImNvbXBvbmVudFdpbGxVbm1vdW50IiwiY2FuY2VsTmV4dENhbGxiYWNrIiwiZ2V0VGltZW91dHMiLCJ0aW1lb3V0IiwibW91bnRpbmciLCJub2RlUmVmIiwiUmVhY3RET00iLCJmaW5kRE9NTm9kZSIsInBlcmZvcm1FbnRlciIsInBlcmZvcm1FeGl0IiwiX3RoaXMyIiwiYXBwZWFyaW5nIiwiX3JlZjIiLCJtYXliZU5vZGUiLCJtYXliZUFwcGVhcmluZyIsInRpbWVvdXRzIiwiZW50ZXJUaW1lb3V0Iiwic2FmZVNldFN0YXRlIiwib25FbnRlcmVkIiwib25FbnRlciIsIm9uRW50ZXJpbmciLCJvblRyYW5zaXRpb25FbmQiLCJfdGhpczMiLCJvbkV4aXRlZCIsIm9uRXhpdCIsIm9uRXhpdGluZyIsImNhbmNlbCIsIm5leHRTdGF0ZSIsImNhbGxiYWNrIiwic2V0TmV4dENhbGxiYWNrIiwiX3RoaXM0IiwiZXZlbnQiLCJkb2VzTm90SGF2ZVRpbWVvdXRPckxpc3RlbmVyIiwiYWRkRW5kTGlzdGVuZXIiLCJzZXRUaW1lb3V0IiwiX3JlZjMiLCJtYXliZU5leHRDYWxsYmFjayIsInJlbmRlciIsIl90aGlzJHByb3BzIiwiY2hpbGRyZW4iLCJjaGlsZFByb3BzIiwiY3JlYXRlRWxlbWVudCIsIlRyYW5zaXRpb25Hcm91cENvbnRleHQiLCJQcm92aWRlciIsImNsb25lRWxlbWVudCIsIkNoaWxkcmVuIiwib25seSIsIkNvbXBvbmVudCIsImNvbnRleHRUeXBlIiwicHJvcFR5cGVzIiwicHQiLCJub29wIiwiZGVmYXVsdFByb3BzIiwib3B0aW9uc1N1cHBvcnRlZCIsIm9uY2VTdXBwb3J0ZWQiLCJvcHRpb25zIiwicGFzc2l2ZSIsIm9uY2UiLCJjYW5Vc2VET00iLCJhZGRFdmVudExpc3RlbmVyIiwicmVtb3ZlRXZlbnRMaXN0ZW5lciIsImUiLCJldmVudE5hbWUiLCJjYXB0dXJlIiwid3JhcHBlZEhhbmRsZXIiLCJfX29uY2UiLCJvbmNlSGFuZGxlciIsImxpc3RlbiIsInRyaWdnZXJFdmVudCIsImJ1YmJsZXMiLCJjYW5jZWxhYmxlIiwiY3JlYXRlRXZlbnQiLCJpbml0RXZlbnQiLCJkaXNwYXRjaEV2ZW50IiwicGFyc2VEdXJhdGlvbiIsInN0ciIsIm11bHQiLCJwYXJzZUZsb2F0IiwiZW11bGF0ZVRyYW5zaXRpb25FbmQiLCJkdXJhdGlvbiIsInBhZGRpbmciLCJjYWxsZWQiLCJoYW5kbGUiLCJyZW1vdmUiLCJjbGVhclRpbWVvdXQiLCJ0cmFuc2l0aW9uRW5kIiwicmVtb3ZlRW11bGF0ZSIsInRyYW5zaXRpb25FbmRMaXN0ZW5lciIsImRlbGF5IiwiY3JlYXRlQ2hhaW5lZEZ1bmN0aW9uIiwiZnVuY3MiLCJmaWx0ZXIiLCJmIiwiYWNjIiwiY2hhaW5lZEZ1bmN0aW9uIiwidHJpZ2dlckJyb3dzZXJSZWZsb3ciLCJvZmZzZXRIZWlnaHQiLCJ0b0ZuUmVmIiwicmVmIiwibWVyZ2VSZWZzIiwicmVmQSIsInJlZkIiLCJhIiwiYiIsInVzZU1lcmdlZFJlZnMiLCJ1c2VNZW1vIiwic2FmZUZpbmRET01Ob2RlIiwiY29tcG9uZW50T3JFbGVtZW50IiwiVHJhbnNpdGlvbldyYXBwZXIiLCJmb3J3YXJkUmVmIiwiY2hpbGRSZWYiLCJtZXJnZWRSZWYiLCJhdHRhY2hSZWYiLCJyIiwibm9ybWFsaXplIiwicGFyYW0iLCJoYW5kbGVFbnRlciIsImhhbmRsZUVudGVyaW5nIiwiaGFuZGxlRW50ZXJlZCIsImhhbmRsZUV4aXQiLCJoYW5kbGVFeGl0aW5nIiwiaGFuZGxlRXhpdGVkIiwiaGFuZGxlQWRkRW5kTGlzdGVuZXIiLCJfanN4IiwiaW5uZXJQcm9wcyIsIk1BUkdJTlMiLCJoZWlnaHQiLCJ3aWR0aCIsImdldERlZmF1bHREaW1lbnNpb25WYWx1ZSIsImRpbWVuc2lvbiIsImVsZW0iLCJvZmZzZXQiLCJzbGljZSIsIm1hcmdpbnMiLCJwYXJzZUludCIsImNvbGxhcHNlU3R5bGVzIiwiZ2V0RGltZW5zaW9uVmFsdWUiLCJDb2xsYXBzZSIsImNsYXNzTmFtZSIsImNvbXB1dGVkRGltZW5zaW9uIiwic2Nyb2xsIiwicm9sZSIsImlzQWNjb3JkaW9uSXRlbVNlbGVjdGVkIiwiYWN0aXZlRXZlbnRLZXkiLCJldmVudEtleSIsImRpc3BsYXlOYW1lIiwiQWNjb3JkaW9uQ29sbGFwc2UiLCJhcyIsImJzUHJlZml4IiwiQWNjb3JkaW9uQ29udGV4dCIsIkFjY29yZGlvbkJvZHkiLCJBY2NvcmRpb25JdGVtQ29udGV4dCIsInVzZUFjY29yZGlvbkJ1dHRvbiIsIm9uQ2xpY2siLCJvblNlbGVjdCIsImFsd2F5c09wZW4iLCJldmVudEtleVBhc3NlZCIsImsiLCJBY2NvcmRpb25CdXR0b24iLCJhY2NvcmRpb25PbkNsaWNrIiwiQWNjb3JkaW9uSGVhZGVyIiwiQWNjb3JkaW9uSXRlbSIsImNvbnRleHRWYWx1ZSIsIkFjY29yZGlvbiIsImFjdGl2ZUtleSIsImZsdXNoIiwiY29udHJvbGxlZFByb3BzIiwiQnV0dG9uIiwiSXRlbSIsIkhlYWRlciIsIkJvZHkiXSwibWFwcGluZ3MiOiI7Ozs7Ozs7Ozs7Ozs7O0FBS0E7O0FBRUMsQ0FBQSxDQUFZLFlBQUE7O0FBR1osR0FBQSxJQUFJQSxNQUFNLEdBQUcsRUFBRSxDQUFDQyxjQUFjLENBQUE7R0FHOUIsU0FBU0MsVUFBVSxHQUFHO0tBQ3JCLElBQUlDLE9BQU8sR0FBRyxFQUFFLENBQUE7QUFFaEIsS0FBQSxLQUFLLElBQUlDLENBQUMsR0FBRyxDQUFDLEVBQUVBLENBQUMsR0FBR0MsU0FBUyxDQUFDQyxNQUFNLEVBQUVGLENBQUMsRUFBRSxFQUFFO0FBQzFDLE9BQUEsSUFBSUcsR0FBRyxHQUFHRixTQUFTLENBQUNELENBQUMsQ0FBQyxDQUFBO09BQ3RCLElBQUksQ0FBQ0csR0FBRyxFQUFFLFNBQUE7T0FFVixJQUFJQyxPQUFPLEdBQUcsT0FBT0QsR0FBRyxDQUFBO09BRXhCLElBQUlDLE9BQU8sS0FBSyxRQUFRLElBQUlBLE9BQU8sS0FBSyxRQUFRLEVBQUU7QUFDakRMLFNBQUFBLE9BQU8sQ0FBQ00sSUFBSSxDQUFDRixHQUFHLENBQUMsQ0FBQTtRQUNqQixNQUFNLElBQUlHLEtBQUssQ0FBQ0MsT0FBTyxDQUFDSixHQUFHLENBQUMsRUFBRTtTQUM5QixJQUFJQSxHQUFHLENBQUNELE1BQU0sRUFBRTtXQUNmLElBQUlNLEtBQUssR0FBR1YsVUFBVSxDQUFDVyxLQUFLLENBQUMsSUFBSSxFQUFFTixHQUFHLENBQUMsQ0FBQTtXQUN2QyxJQUFJSyxLQUFLLEVBQUU7QUFDVlQsYUFBQUEsT0FBTyxDQUFDTSxJQUFJLENBQUNHLEtBQUssQ0FBQyxDQUFBO1lBQ3BCO1VBQ0Q7QUFDRCxRQUFDLE1BQU0sSUFBSUosT0FBTyxLQUFLLFFBQVEsRUFBRTtTQUNoQyxJQUFJRCxHQUFHLENBQUNPLFFBQVEsS0FBS0MsTUFBTSxDQUFDQyxTQUFTLENB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
