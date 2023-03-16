define(['exports', 'react', 'react/jsx-runtime', 'react-dom'], (function (exports, React, jsxRuntime, ReactDOM) { 'use strict';

	function _interopDefaultLegacy (e) { return e && typeof e === 'object' && 'default' in e ? e : { 'default': e }; }

	function _interopNamespace(e) {
		if (e && e.__esModule) return e;
		var n = Object.create(null);
		if (e) {
			Object.keys(e).forEach(function (k) {
				if (k !== 'default') {
					var d = Object.getOwnPropertyDescriptor(e, k);
					Object.defineProperty(n, k, d.get ? d : {
						enumerable: true,
						get: function () { return e[k]; }
					});
				}
			});
		}
		n["default"] = e;
		return Object.freeze(n);
	}

	var React__namespace = /*#__PURE__*/_interopNamespace(React);
	var React__default = /*#__PURE__*/_interopDefaultLegacy(React);
	var ReactDOM__default = /*#__PURE__*/_interopDefaultLegacy(ReactDOM);

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
	  var wasPropRef = React.useRef(propValue !== undefined);
	  var _useState = React.useState(defaultValue),
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
	  return [isProp ? propValue : stateValue, React.useCallback(function (value) {
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
	const ThemeContext = /*#__PURE__*/React__namespace.createContext({
	  prefixes: {},
	  breakpoints: DEFAULT_BREAKPOINTS,
	  minBreakpoint: DEFAULT_MIN_BREAKPOINT
	});
	function useBootstrapPrefix(prefix, defaultPrefix) {
	  const {
	    prefixes
	  } = React.useContext(ThemeContext);
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

	var TransitionGroupContext = React__default["default"].createContext(null);

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
	          var node = this.props.nodeRef ? this.props.nodeRef.current : ReactDOM__default["default"].findDOMNode(this); // https://github.com/reactjs/react-transition-group/pull/749
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
	    var _ref2 = this.props.nodeRef ? [appearing] : [ReactDOM__default["default"].findDOMNode(this), appearing],
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
	    var maybeNode = this.props.nodeRef ? undefined : ReactDOM__default["default"].findDOMNode(this); // no exit animation skip right to EXITED

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
	    var node = this.props.nodeRef ? this.props.nodeRef.current : ReactDOM__default["default"].findDOMNode(this);
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
	      React__default["default"].createElement(TransitionGroupContext.Provider, {
	        value: null
	      }, typeof children === 'function' ? children(status, childProps) : React__default["default"].cloneElement(React__default["default"].Children.only(children), childProps))
	    );
	  };
	  return Transition;
	}(React__default["default"].Component);
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
	  return React.useMemo(function () {
	    return mergeRefs(refA, refB);
	  }, [refA, refB]);
	}

	function safeFindDOMNode(componentOrElement) {
	  if (componentOrElement && 'setState' in componentOrElement) {
	    return ReactDOM__default["default"].findDOMNode(componentOrElement);
	  }
	  return componentOrElement != null ? componentOrElement : null;
	}

	// Normalizes Transition callbacks when nodeRef is used.
	const TransitionWrapper = /*#__PURE__*/React__default["default"].forwardRef(({
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
	  const nodeRef = React.useRef(null);
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
	  const handleEnter = React.useCallback(normalize(onEnter), [onEnter]);
	  const handleEntering = React.useCallback(normalize(onEntering), [onEntering]);
	  const handleEntered = React.useCallback(normalize(onEntered), [onEntered]);
	  const handleExit = React.useCallback(normalize(onExit), [onExit]);
	  const handleExiting = React.useCallback(normalize(onExiting), [onExiting]);
	  const handleExited = React.useCallback(normalize(onExited), [onExited]);
	  const handleAddEndListener = React.useCallback(normalize(addEndListener), [addEndListener]);
	  /* eslint-enable react-hooks/exhaustive-deps */

	  return /*#__PURE__*/jsxRuntime.jsx(Transition, {
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
	    }) : /*#__PURE__*/React__default["default"].cloneElement(children, {
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
	const Collapse = /*#__PURE__*/React__default["default"].forwardRef(({
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
	  const handleEnter = React.useMemo(() => createChainedFunction(elem => {
	    elem.style[computedDimension] = '0';
	  }, onEnter), [computedDimension, onEnter]);
	  const handleEntering = React.useMemo(() => createChainedFunction(elem => {
	    const scroll = `scroll${computedDimension[0].toUpperCase()}${computedDimension.slice(1)}`;
	    elem.style[computedDimension] = `${elem[scroll]}px`;
	  }, onEntering), [computedDimension, onEntering]);
	  const handleEntered = React.useMemo(() => createChainedFunction(elem => {
	    elem.style[computedDimension] = null;
	  }, onEntered), [computedDimension, onEntered]);

	  /* -- Collapsing -- */
	  const handleExit = React.useMemo(() => createChainedFunction(elem => {
	    elem.style[computedDimension] = `${getDimensionValue(computedDimension, elem)}px`;
	    triggerBrowserReflow(elem);
	  }, onExit), [onExit, getDimensionValue, computedDimension]);
	  const handleExiting = React.useMemo(() => createChainedFunction(elem => {
	    elem.style[computedDimension] = null;
	  }, onExiting), [computedDimension, onExiting]);
	  return /*#__PURE__*/jsxRuntime.jsx(TransitionWrapper, {
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
	    children: (state, innerProps) => /*#__PURE__*/React__default["default"].cloneElement(children, {
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
	const context$1 = /*#__PURE__*/React__namespace.createContext({});
	context$1.displayName = 'AccordionContext';

	/**
	 * This component accepts all of [`Collapse`'s props](/utilities/transitions/#collapse-props).
	 */
	const AccordionCollapse = /*#__PURE__*/React__namespace.forwardRef(({
	  as: Component = 'div',
	  bsPrefix,
	  className,
	  children,
	  eventKey,
	  ...props
	}, ref) => {
	  const {
	    activeEventKey
	  } = React.useContext(context$1);
	  bsPrefix = useBootstrapPrefix(bsPrefix, 'accordion-collapse');
	  return /*#__PURE__*/jsxRuntime.jsx(Collapse, {
	    ref: ref,
	    in: isAccordionItemSelected(activeEventKey, eventKey),
	    ...props,
	    className: classNames(className, bsPrefix),
	    children: /*#__PURE__*/jsxRuntime.jsx(Component, {
	      children: React__namespace.Children.only(children)
	    })
	  });
	});
	AccordionCollapse.displayName = 'AccordionCollapse';

	const context = /*#__PURE__*/React__namespace.createContext({
	  eventKey: ''
	});
	context.displayName = 'AccordionItemContext';

	const AccordionBody = /*#__PURE__*/React__namespace.forwardRef(({
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
	  } = React.useContext(context);
	  return /*#__PURE__*/jsxRuntime.jsx(AccordionCollapse, {
	    eventKey: eventKey,
	    onEnter: onEnter,
	    onEntering: onEntering,
	    onEntered: onEntered,
	    onExit: onExit,
	    onExiting: onExiting,
	    onExited: onExited,
	    children: /*#__PURE__*/jsxRuntime.jsx(Component, {
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
	  } = React.useContext(context$1);
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
	const AccordionButton = /*#__PURE__*/React__namespace.forwardRef(({
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
	  } = React.useContext(context);
	  const accordionOnClick = useAccordionButton(eventKey, onClick);
	  const {
	    activeEventKey
	  } = React.useContext(context$1);
	  if (Component === 'button') {
	    props.type = 'button';
	  }
	  return /*#__PURE__*/jsxRuntime.jsx(Component, {
	    ref: ref,
	    onClick: accordionOnClick,
	    ...props,
	    "aria-expanded": eventKey === activeEventKey,
	    className: classNames(className, bsPrefix, !isAccordionItemSelected(activeEventKey, eventKey) && 'collapsed')
	  });
	});
	AccordionButton.displayName = 'AccordionButton';

	const AccordionHeader = /*#__PURE__*/React__namespace.forwardRef(({
	  // Need to define the default "as" during prop destructuring to be compatible with styled-components github.com/react-bootstrap/react-bootstrap/issues/3595
	  as: Component = 'h2',
	  bsPrefix,
	  className,
	  children,
	  onClick,
	  ...props
	}, ref) => {
	  bsPrefix = useBootstrapPrefix(bsPrefix, 'accordion-header');
	  return /*#__PURE__*/jsxRuntime.jsx(Component, {
	    ref: ref,
	    ...props,
	    className: classNames(className, bsPrefix),
	    children: /*#__PURE__*/jsxRuntime.jsx(AccordionButton, {
	      onClick: onClick,
	      children: children
	    })
	  });
	});
	AccordionHeader.displayName = 'AccordionHeader';

	const AccordionItem = /*#__PURE__*/React__namespace.forwardRef(({
	  // Need to define the default "as" during prop destructuring to be compatible with styled-components github.com/react-bootstrap/react-bootstrap/issues/3595
	  as: Component = 'div',
	  bsPrefix,
	  className,
	  eventKey,
	  ...props
	}, ref) => {
	  bsPrefix = useBootstrapPrefix(bsPrefix, 'accordion-item');
	  const contextValue = React.useMemo(() => ({
	    eventKey
	  }), [eventKey]);
	  return /*#__PURE__*/jsxRuntime.jsx(context.Provider, {
	    value: contextValue,
	    children: /*#__PURE__*/jsxRuntime.jsx(Component, {
	      ref: ref,
	      ...props,
	      className: classNames(className, bsPrefix)
	    })
	  });
	});
	AccordionItem.displayName = 'AccordionItem';

	const Accordion = /*#__PURE__*/React__namespace.forwardRef((props, ref) => {
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
	  const contextValue = React.useMemo(() => ({
	    activeEventKey: activeKey,
	    onSelect,
	    alwaysOpen
	  }), [activeKey, onSelect, alwaysOpen]);
	  return /*#__PURE__*/jsxRuntime.jsx(context$1.Provider, {
	    value: contextValue,
	    children: /*#__PURE__*/jsxRuntime.jsx(Component, {
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

	class Accordian extends React.Component {
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
	        return (React.createElement(Accordion$1, { defaultActiveKey: this.handledefaultopen },
	            React.createElement(Accordion$1.Item, { eventKey: "0" },
	                React.createElement(Accordion$1.Header, { className: "AccordianHeader" }, this.header),
	                React.createElement(Accordion$1.Body, { onEnter: this.handleEnter, onExit: this.handleExit }, this.props.content))));
	    }
	}

	exports.Accordian = Accordian;

	Object.defineProperty(exports, '__esModule', { value: true });

}));
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiQWNjb3JkaWFuLmpzIiwic291cmNlcyI6WyIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvY2xhc3NuYW1lcy9pbmRleC5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9AYmFiZWwvcnVudGltZS9oZWxwZXJzL2VzbS9leHRlbmRzLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL0BiYWJlbC9ydW50aW1lL2hlbHBlcnMvZXNtL29iamVjdFdpdGhvdXRQcm9wZXJ0aWVzTG9vc2UuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvdW5jb250cm9sbGFibGUvbGliL2VzbS91dGlscy5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy91bmNvbnRyb2xsYWJsZS9saWIvZXNtL2hvb2suanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvQGJhYmVsL3J1bnRpbWUvaGVscGVycy9lc20vc2V0UHJvdG90eXBlT2YuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvQGJhYmVsL3J1bnRpbWUvaGVscGVycy9lc20vaW5oZXJpdHNMb29zZS5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9yZWFjdC1ib290c3RyYXAvZXNtL1RoZW1lUHJvdmlkZXIuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvZG9tLWhlbHBlcnMvZXNtL293bmVyRG9jdW1lbnQuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvZG9tLWhlbHBlcnMvZXNtL293bmVyV2luZG93LmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL2RvbS1oZWxwZXJzL2VzbS9nZXRDb21wdXRlZFN0eWxlLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL2RvbS1oZWxwZXJzL2VzbS9oeXBoZW5hdGUuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvZG9tLWhlbHBlcnMvZXNtL2h5cGhlbmF0ZVN0eWxlLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL2RvbS1oZWxwZXJzL2VzbS9pc1RyYW5zZm9ybS5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9kb20taGVscGVycy9lc20vY3NzLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3Byb3AtdHlwZXMvbm9kZV9tb2R1bGVzL3JlYWN0LWlzL2Nqcy9yZWFjdC1pcy5kZXZlbG9wbWVudC5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9wcm9wLXR5cGVzL25vZGVfbW9kdWxlcy9yZWFjdC1pcy9pbmRleC5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9vYmplY3QtYXNzaWduL2luZGV4LmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3Byb3AtdHlwZXMvbGliL1JlYWN0UHJvcFR5cGVzU2VjcmV0LmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3Byb3AtdHlwZXMvbGliL2hhcy5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9wcm9wLXR5cGVzL2NoZWNrUHJvcFR5cGVzLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3Byb3AtdHlwZXMvZmFjdG9yeVdpdGhUeXBlQ2hlY2tlcnMuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcHJvcC10eXBlcy9pbmRleC5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9yZWFjdC10cmFuc2l0aW9uLWdyb3VwL2VzbS9jb25maWcuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtdHJhbnNpdGlvbi1ncm91cC9lc20vdXRpbHMvUHJvcFR5cGVzLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvZXNtL1RyYW5zaXRpb25Hcm91cENvbnRleHQuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtdHJhbnNpdGlvbi1ncm91cC9lc20vdXRpbHMvcmVmbG93LmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvZXNtL1RyYW5zaXRpb24uanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvZG9tLWhlbHBlcnMvZXNtL2NhblVzZURPTS5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9kb20taGVscGVycy9lc20vYWRkRXZlbnRMaXN0ZW5lci5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9kb20taGVscGVycy9lc20vcmVtb3ZlRXZlbnRMaXN0ZW5lci5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9kb20taGVscGVycy9lc20vbGlzdGVuLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL2RvbS1oZWxwZXJzL2VzbS90cmlnZ2VyRXZlbnQuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvZG9tLWhlbHBlcnMvZXNtL3RyYW5zaXRpb25FbmQuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS90cmFuc2l0aW9uRW5kTGlzdGVuZXIuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS9jcmVhdGVDaGFpbmVkRnVuY3Rpb24uanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS90cmlnZ2VyQnJvd3NlclJlZmxvdy5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9AcmVzdGFydC9ob29rcy9lc20vdXNlTWVyZ2VkUmVmcy5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9yZWFjdC1ib290c3RyYXAvZXNtL3NhZmVGaW5kRE9NTm9kZS5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9yZWFjdC1ib290c3RyYXAvZXNtL1RyYW5zaXRpb25XcmFwcGVyLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LWJvb3RzdHJhcC9lc20vQ29sbGFwc2UuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS9BY2NvcmRpb25Db250ZXh0LmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LWJvb3RzdHJhcC9lc20vQWNjb3JkaW9uQ29sbGFwc2UuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS9BY2NvcmRpb25JdGVtQ29udGV4dC5qcyIsIi4uLy4uLy4uLy4uLy4uL25vZGVfbW9kdWxlcy9yZWFjdC1ib290c3RyYXAvZXNtL0FjY29yZGlvbkJvZHkuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS9BY2NvcmRpb25CdXR0b24uanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS9BY2NvcmRpb25IZWFkZXIuanMiLCIuLi8uLi8uLi8uLi8uLi9ub2RlX21vZHVsZXMvcmVhY3QtYm9vdHN0cmFwL2VzbS9BY2NvcmRpb25JdGVtLmpzIiwiLi4vLi4vLi4vLi4vLi4vbm9kZV9tb2R1bGVzL3JlYWN0LWJvb3RzdHJhcC9lc20vQWNjb3JkaW9uLmpzIiwiLi4vLi4vLi4vLi4vLi4vc3JjL0FjY29yZGlhbi50c3giXSwic291cmNlc0NvbnRlbnQiOlsiLyohXG5cdENvcHlyaWdodCAoYykgMjAxOCBKZWQgV2F0c29uLlxuXHRMaWNlbnNlZCB1bmRlciB0aGUgTUlUIExpY2Vuc2UgKE1JVCksIHNlZVxuXHRodHRwOi8vamVkd2F0c29uLmdpdGh1Yi5pby9jbGFzc25hbWVzXG4qL1xuLyogZ2xvYmFsIGRlZmluZSAqL1xuXG4oZnVuY3Rpb24gKCkge1xuXHQndXNlIHN0cmljdCc7XG5cblx0dmFyIGhhc093biA9IHt9Lmhhc093blByb3BlcnR5O1xuXHR2YXIgbmF0aXZlQ29kZVN0cmluZyA9ICdbbmF0aXZlIGNvZGVdJztcblxuXHRmdW5jdGlvbiBjbGFzc05hbWVzKCkge1xuXHRcdHZhciBjbGFzc2VzID0gW107XG5cblx0XHRmb3IgKHZhciBpID0gMDsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuXHRcdFx0dmFyIGFyZyA9IGFyZ3VtZW50c1tpXTtcblx0XHRcdGlmICghYXJnKSBjb250aW51ZTtcblxuXHRcdFx0dmFyIGFyZ1R5cGUgPSB0eXBlb2YgYXJnO1xuXG5cdFx0XHRpZiAoYXJnVHlwZSA9PT0gJ3N0cmluZycgfHwgYXJnVHlwZSA9PT0gJ251bWJlcicpIHtcblx0XHRcdFx0Y2xhc3Nlcy5wdXNoKGFyZyk7XG5cdFx0XHR9IGVsc2UgaWYgKEFycmF5LmlzQXJyYXkoYXJnKSkge1xuXHRcdFx0XHRpZiAoYXJnLmxlbmd0aCkge1xuXHRcdFx0XHRcdHZhciBpbm5lciA9IGNsYXNzTmFtZXMuYXBwbHkobnVsbCwgYXJnKTtcblx0XHRcdFx0XHRpZiAoaW5uZXIpIHtcblx0XHRcdFx0XHRcdGNsYXNzZXMucHVzaChpbm5lcik7XG5cdFx0XHRcdFx0fVxuXHRcdFx0XHR9XG5cdFx0XHR9IGVsc2UgaWYgKGFyZ1R5cGUgPT09ICdvYmplY3QnKSB7XG5cdFx0XHRcdGlmIChhcmcudG9TdHJpbmcgIT09IE9iamVjdC5wcm90b3R5cGUudG9TdHJpbmcgJiYgIWFyZy50b1N0cmluZy50b1N0cmluZygpLmluY2x1ZGVzKCdbbmF0aXZlIGNvZGVdJykpIHtcblx0XHRcdFx0XHRjbGFzc2VzLnB1c2goYXJnLnRvU3RyaW5nKCkpO1xuXHRcdFx0XHRcdGNvbnRpbnVlO1xuXHRcdFx0XHR9XG5cblx0XHRcdFx0Zm9yICh2YXIga2V5IGluIGFyZykge1xuXHRcdFx0XHRcdGlmIChoYXNPd24uY2FsbChhcmcsIGtleSkgJiYgYXJnW2tleV0pIHtcblx0XHRcdFx0XHRcdGNsYXNzZXMucHVzaChrZXkpO1xuXHRcdFx0XHRcdH1cblx0XHRcdFx0fVxuXHRcdFx0fVxuXHRcdH1cblxuXHRcdHJldHVybiBjbGFzc2VzLmpvaW4oJyAnKTtcblx0fVxuXG5cdGlmICh0eXBlb2YgbW9kdWxlICE9PSAndW5kZWZpbmVkJyAmJiBtb2R1bGUuZXhwb3J0cykge1xuXHRcdGNsYXNzTmFtZXMuZGVmYXVsdCA9IGNsYXNzTmFtZXM7XG5cdFx0bW9kdWxlLmV4cG9ydHMgPSBjbGFzc05hbWVzO1xuXHR9IGVsc2UgaWYgKHR5cGVvZiBkZWZpbmUgPT09ICdmdW5jdGlvbicgJiYgdHlwZW9mIGRlZmluZS5hbWQgPT09ICdvYmplY3QnICYmIGRlZmluZS5hbWQpIHtcblx0XHQvLyByZWdpc3RlciBhcyAnY2xhc3NuYW1lcycsIGNvbnNpc3RlbnQgd2l0aCBucG0gcGFja2FnZSBuYW1lXG5cdFx0ZGVmaW5lKCdjbGFzc25hbWVzJywgW10sIGZ1bmN0aW9uICgpIHtcblx0XHRcdHJldHVybiBjbGFzc05hbWVzO1xuXHRcdH0pO1xuXHR9IGVsc2Uge1xuXHRcdHdpbmRvdy5jbGFzc05hbWVzID0gY2xhc3NOYW1lcztcblx0fVxufSgpKTtcbiIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIF9leHRlbmRzKCkge1xuICBfZXh0ZW5kcyA9IE9iamVjdC5hc3NpZ24gPyBPYmplY3QuYXNzaWduLmJpbmQoKSA6IGZ1bmN0aW9uICh0YXJnZXQpIHtcbiAgICBmb3IgKHZhciBpID0gMTsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykge1xuICAgICAgdmFyIHNvdXJjZSA9IGFyZ3VtZW50c1tpXTtcbiAgICAgIGZvciAodmFyIGtleSBpbiBzb3VyY2UpIHtcbiAgICAgICAgaWYgKE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChzb3VyY2UsIGtleSkpIHtcbiAgICAgICAgICB0YXJnZXRba2V5XSA9IHNvdXJjZVtrZXldO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgfVxuICAgIHJldHVybiB0YXJnZXQ7XG4gIH07XG4gIHJldHVybiBfZXh0ZW5kcy5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xufSIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIF9vYmplY3RXaXRob3V0UHJvcGVydGllc0xvb3NlKHNvdXJjZSwgZXhjbHVkZWQpIHtcbiAgaWYgKHNvdXJjZSA9PSBudWxsKSByZXR1cm4ge307XG4gIHZhciB0YXJnZXQgPSB7fTtcbiAgdmFyIHNvdXJjZUtleXMgPSBPYmplY3Qua2V5cyhzb3VyY2UpO1xuICB2YXIga2V5LCBpO1xuICBmb3IgKGkgPSAwOyBpIDwgc291cmNlS2V5cy5sZW5ndGg7IGkrKykge1xuICAgIGtleSA9IHNvdXJjZUtleXNbaV07XG4gICAgaWYgKGV4Y2x1ZGVkLmluZGV4T2Yoa2V5KSA+PSAwKSBjb250aW51ZTtcbiAgICB0YXJnZXRba2V5XSA9IHNvdXJjZVtrZXldO1xuICB9XG4gIHJldHVybiB0YXJnZXQ7XG59IiwiaW1wb3J0IGludmFyaWFudCBmcm9tICdpbnZhcmlhbnQnO1xuXG52YXIgbm9vcCA9IGZ1bmN0aW9uIG5vb3AoKSB7fTtcblxuZnVuY3Rpb24gcmVhZE9ubHlQcm9wVHlwZShoYW5kbGVyLCBuYW1lKSB7XG4gIHJldHVybiBmdW5jdGlvbiAocHJvcHMsIHByb3BOYW1lKSB7XG4gICAgaWYgKHByb3BzW3Byb3BOYW1lXSAhPT0gdW5kZWZpbmVkKSB7XG4gICAgICBpZiAoIXByb3BzW2hhbmRsZXJdKSB7XG4gICAgICAgIHJldHVybiBuZXcgRXJyb3IoXCJZb3UgaGF2ZSBwcm92aWRlZCBhIGBcIiArIHByb3BOYW1lICsgXCJgIHByb3AgdG8gYFwiICsgbmFtZSArIFwiYCBcIiArIChcIndpdGhvdXQgYW4gYFwiICsgaGFuZGxlciArIFwiYCBoYW5kbGVyIHByb3AuIFRoaXMgd2lsbCByZW5kZXIgYSByZWFkLW9ubHkgZmllbGQuIFwiKSArIChcIklmIHRoZSBmaWVsZCBzaG91bGQgYmUgbXV0YWJsZSB1c2UgYFwiICsgZGVmYXVsdEtleShwcm9wTmFtZSkgKyBcImAuIFwiKSArIChcIk90aGVyd2lzZSwgc2V0IGBcIiArIGhhbmRsZXIgKyBcImAuXCIpKTtcbiAgICAgIH1cbiAgICB9XG4gIH07XG59XG5cbmV4cG9ydCBmdW5jdGlvbiB1bmNvbnRyb2xsZWRQcm9wVHlwZXMoY29udHJvbGxlZFZhbHVlcywgZGlzcGxheU5hbWUpIHtcbiAgdmFyIHByb3BUeXBlcyA9IHt9O1xuICBPYmplY3Qua2V5cyhjb250cm9sbGVkVmFsdWVzKS5mb3JFYWNoKGZ1bmN0aW9uIChwcm9wKSB7XG4gICAgLy8gYWRkIGRlZmF1bHQgcHJvcFR5cGVzIGZvciBmb2xrcyB0aGF0IHVzZSBydW50aW1lIGNoZWNrc1xuICAgIHByb3BUeXBlc1tkZWZhdWx0S2V5KHByb3ApXSA9IG5vb3A7XG5cbiAgICBpZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09ICdwcm9kdWN0aW9uJykge1xuICAgICAgdmFyIGhhbmRsZXIgPSBjb250cm9sbGVkVmFsdWVzW3Byb3BdO1xuICAgICAgISh0eXBlb2YgaGFuZGxlciA9PT0gJ3N0cmluZycgJiYgaGFuZGxlci50cmltKCkubGVuZ3RoKSA/IHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSBcInByb2R1Y3Rpb25cIiA/IGludmFyaWFudChmYWxzZSwgJ1VuY29udHJvbGxhYmxlIC0gWyVzXTogdGhlIHByb3AgYCVzYCBuZWVkcyBhIHZhbGlkIGhhbmRsZXIga2V5IG5hbWUgaW4gb3JkZXIgdG8gbWFrZSBpdCB1bmNvbnRyb2xsYWJsZScsIGRpc3BsYXlOYW1lLCBwcm9wKSA6IGludmFyaWFudChmYWxzZSkgOiB2b2lkIDA7XG4gICAgICBwcm9wVHlwZXNbcHJvcF0gPSByZWFkT25seVByb3BUeXBlKGhhbmRsZXIsIGRpc3BsYXlOYW1lKTtcbiAgICB9XG4gIH0pO1xuICByZXR1cm4gcHJvcFR5cGVzO1xufVxuZXhwb3J0IGZ1bmN0aW9uIGlzUHJvcChwcm9wcywgcHJvcCkge1xuICByZXR1cm4gcHJvcHNbcHJvcF0gIT09IHVuZGVmaW5lZDtcbn1cbmV4cG9ydCBmdW5jdGlvbiBkZWZhdWx0S2V5KGtleSkge1xuICByZXR1cm4gJ2RlZmF1bHQnICsga2V5LmNoYXJBdCgwKS50b1VwcGVyQ2FzZSgpICsga2V5LnN1YnN0cigxKTtcbn1cbi8qKlxuICogQ29weXJpZ2h0IChjKSAyMDEzLXByZXNlbnQsIEZhY2Vib29rLCBJbmMuXG4gKiBBbGwgcmlnaHRzIHJlc2VydmVkLlxuICpcbiAqIFRoaXMgc291cmNlIGNvZGUgaXMgbGljZW5zZWQgdW5kZXIgdGhlIEJTRC1zdHlsZSBsaWNlbnNlIGZvdW5kIGluIHRoZVxuICogTElDRU5TRSBmaWxlIGluIHRoZSByb290IGRpcmVjdG9yeSBvZiB0aGlzIHNvdXJjZSB0cmVlLiBBbiBhZGRpdGlvbmFsIGdyYW50XG4gKiBvZiBwYXRlbnQgcmlnaHRzIGNhbiBiZSBmb3VuZCBpbiB0aGUgUEFURU5UUyBmaWxlIGluIHRoZSBzYW1lIGRpcmVjdG9yeS5cbiAqL1xuXG5leHBvcnQgZnVuY3Rpb24gY2FuQWNjZXB0UmVmKGNvbXBvbmVudCkge1xuICByZXR1cm4gISFjb21wb25lbnQgJiYgKHR5cGVvZiBjb21wb25lbnQgIT09ICdmdW5jdGlvbicgfHwgY29tcG9uZW50LnByb3RvdHlwZSAmJiBjb21wb25lbnQucHJvdG90eXBlLmlzUmVhY3RDb21wb25lbnQpO1xufSIsImltcG9ydCBfZXh0ZW5kcyBmcm9tIFwiQGJhYmVsL3J1bnRpbWUvaGVscGVycy9lc20vZXh0ZW5kc1wiO1xuaW1wb3J0IF9vYmplY3RXaXRob3V0UHJvcGVydGllc0xvb3NlIGZyb20gXCJAYmFiZWwvcnVudGltZS9oZWxwZXJzL2VzbS9vYmplY3RXaXRob3V0UHJvcGVydGllc0xvb3NlXCI7XG5cbmZ1bmN0aW9uIF90b1Byb3BlcnR5S2V5KGFyZykgeyB2YXIga2V5ID0gX3RvUHJpbWl0aXZlKGFyZywgXCJzdHJpbmdcIik7IHJldHVybiB0eXBlb2Yga2V5ID09PSBcInN5bWJvbFwiID8ga2V5IDogU3RyaW5nKGtleSk7IH1cblxuZnVuY3Rpb24gX3RvUHJpbWl0aXZlKGlucHV0LCBoaW50KSB7IGlmICh0eXBlb2YgaW5wdXQgIT09IFwib2JqZWN0XCIgfHwgaW5wdXQgPT09IG51bGwpIHJldHVybiBpbnB1dDsgdmFyIHByaW0gPSBpbnB1dFtTeW1ib2wudG9QcmltaXRpdmVdOyBpZiAocHJpbSAhPT0gdW5kZWZpbmVkKSB7IHZhciByZXMgPSBwcmltLmNhbGwoaW5wdXQsIGhpbnQgfHwgXCJkZWZhdWx0XCIpOyBpZiAodHlwZW9mIHJlcyAhPT0gXCJvYmplY3RcIikgcmV0dXJuIHJlczsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkBAdG9QcmltaXRpdmUgbXVzdCByZXR1cm4gYSBwcmltaXRpdmUgdmFsdWUuXCIpOyB9IHJldHVybiAoaGludCA9PT0gXCJzdHJpbmdcIiA/IFN0cmluZyA6IE51bWJlcikoaW5wdXQpOyB9XG5cbmltcG9ydCB7IHVzZUNhbGxiYWNrLCB1c2VSZWYsIHVzZVN0YXRlIH0gZnJvbSAncmVhY3QnO1xuaW1wb3J0ICogYXMgVXRpbHMgZnJvbSAnLi91dGlscyc7XG5cbmZ1bmN0aW9uIHVzZVVuY29udHJvbGxlZFByb3AocHJvcFZhbHVlLCBkZWZhdWx0VmFsdWUsIGhhbmRsZXIpIHtcbiAgdmFyIHdhc1Byb3BSZWYgPSB1c2VSZWYocHJvcFZhbHVlICE9PSB1bmRlZmluZWQpO1xuXG4gIHZhciBfdXNlU3RhdGUgPSB1c2VTdGF0ZShkZWZhdWx0VmFsdWUpLFxuICAgICAgc3RhdGVWYWx1ZSA9IF91c2VTdGF0ZVswXSxcbiAgICAgIHNldFN0YXRlID0gX3VzZVN0YXRlWzFdO1xuXG4gIHZhciBpc1Byb3AgPSBwcm9wVmFsdWUgIT09IHVuZGVmaW5lZDtcbiAgdmFyIHdhc1Byb3AgPSB3YXNQcm9wUmVmLmN1cnJlbnQ7XG4gIHdhc1Byb3BSZWYuY3VycmVudCA9IGlzUHJvcDtcbiAgLyoqXG4gICAqIElmIGEgcHJvcCBzd2l0Y2hlcyBmcm9tIGNvbnRyb2xsZWQgdG8gVW5jb250cm9sbGVkXG4gICAqIHJlc2V0IGl0cyB2YWx1ZSB0byB0aGUgZGVmYXVsdFZhbHVlXG4gICAqL1xuXG4gIGlmICghaXNQcm9wICYmIHdhc1Byb3AgJiYgc3RhdGVWYWx1ZSAhPT0gZGVmYXVsdFZhbHVlKSB7XG4gICAgc2V0U3RhdGUoZGVmYXVsdFZhbHVlKTtcbiAgfVxuXG4gIHJldHVybiBbaXNQcm9wID8gcHJvcFZhbHVlIDogc3RhdGVWYWx1ZSwgdXNlQ2FsbGJhY2soZnVuY3Rpb24gKHZhbHVlKSB7XG4gICAgZm9yICh2YXIgX2xlbiA9IGFyZ3VtZW50cy5sZW5ndGgsIGFyZ3MgPSBuZXcgQXJyYXkoX2xlbiA+IDEgPyBfbGVuIC0gMSA6IDApLCBfa2V5ID0gMTsgX2tleSA8IF9sZW47IF9rZXkrKykge1xuICAgICAgYXJnc1tfa2V5IC0gMV0gPSBhcmd1bWVudHNbX2tleV07XG4gICAgfVxuXG4gICAgaWYgKGhhbmRsZXIpIGhhbmRsZXIuYXBwbHkodm9pZCAwLCBbdmFsdWVdLmNvbmNhdChhcmdzKSk7XG4gICAgc2V0U3RhdGUodmFsdWUpO1xuICB9LCBbaGFuZGxlcl0pXTtcbn1cblxuZXhwb3J0IHsgdXNlVW5jb250cm9sbGVkUHJvcCB9O1xuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gdXNlVW5jb250cm9sbGVkKHByb3BzLCBjb25maWcpIHtcbiAgcmV0dXJuIE9iamVjdC5rZXlzKGNvbmZpZykucmVkdWNlKGZ1bmN0aW9uIChyZXN1bHQsIGZpZWxkTmFtZSkge1xuICAgIHZhciBfZXh0ZW5kczI7XG5cbiAgICB2YXIgX3JlZiA9IHJlc3VsdCxcbiAgICAgICAgZGVmYXVsdFZhbHVlID0gX3JlZltVdGlscy5kZWZhdWx0S2V5KGZpZWxkTmFtZSldLFxuICAgICAgICBwcm9wc1ZhbHVlID0gX3JlZltmaWVsZE5hbWVdLFxuICAgICAgICByZXN0ID0gX29iamVjdFdpdGhvdXRQcm9wZXJ0aWVzTG9vc2UoX3JlZiwgW1V0aWxzLmRlZmF1bHRLZXkoZmllbGROYW1lKSwgZmllbGROYW1lXS5tYXAoX3RvUHJvcGVydHlLZXkpKTtcblxuICAgIHZhciBoYW5kbGVyTmFtZSA9IGNvbmZpZ1tmaWVsZE5hbWVdO1xuXG4gICAgdmFyIF91c2VVbmNvbnRyb2xsZWRQcm9wID0gdXNlVW5jb250cm9sbGVkUHJvcChwcm9wc1ZhbHVlLCBkZWZhdWx0VmFsdWUsIHByb3BzW2hhbmRsZXJOYW1lXSksXG4gICAgICAgIHZhbHVlID0gX3VzZVVuY29udHJvbGxlZFByb3BbMF0sXG4gICAgICAgIGhhbmRsZXIgPSBfdXNlVW5jb250cm9sbGVkUHJvcFsxXTtcblxuICAgIHJldHVybiBfZXh0ZW5kcyh7fSwgcmVzdCwgKF9leHRlbmRzMiA9IHt9LCBfZXh0ZW5kczJbZmllbGROYW1lXSA9IHZhbHVlLCBfZXh0ZW5kczJbaGFuZGxlck5hbWVdID0gaGFuZGxlciwgX2V4dGVuZHMyKSk7XG4gIH0sIHByb3BzKTtcbn0iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBfc2V0UHJvdG90eXBlT2YobywgcCkge1xuICBfc2V0UHJvdG90eXBlT2YgPSBPYmplY3Quc2V0UHJvdG90eXBlT2YgPyBPYmplY3Quc2V0UHJvdG90eXBlT2YuYmluZCgpIDogZnVuY3Rpb24gX3NldFByb3RvdHlwZU9mKG8sIHApIHtcbiAgICBvLl9fcHJvdG9fXyA9IHA7XG4gICAgcmV0dXJuIG87XG4gIH07XG4gIHJldHVybiBfc2V0UHJvdG90eXBlT2YobywgcCk7XG59IiwiaW1wb3J0IHNldFByb3RvdHlwZU9mIGZyb20gXCIuL3NldFByb3RvdHlwZU9mLmpzXCI7XG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBfaW5oZXJpdHNMb29zZShzdWJDbGFzcywgc3VwZXJDbGFzcykge1xuICBzdWJDbGFzcy5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKHN1cGVyQ2xhc3MucHJvdG90eXBlKTtcbiAgc3ViQ2xhc3MucHJvdG90eXBlLmNvbnN0cnVjdG9yID0gc3ViQ2xhc3M7XG4gIHNldFByb3RvdHlwZU9mKHN1YkNsYXNzLCBzdXBlckNsYXNzKTtcbn0iLCJpbXBvcnQgKiBhcyBSZWFjdCBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyB1c2VDb250ZXh0LCB1c2VNZW1vIH0gZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsganN4IGFzIF9qc3ggfSBmcm9tIFwicmVhY3QvanN4LXJ1bnRpbWVcIjtcbmV4cG9ydCBjb25zdCBERUZBVUxUX0JSRUFLUE9JTlRTID0gWyd4eGwnLCAneGwnLCAnbGcnLCAnbWQnLCAnc20nLCAneHMnXTtcbmV4cG9ydCBjb25zdCBERUZBVUxUX01JTl9CUkVBS1BPSU5UID0gJ3hzJztcbmNvbnN0IFRoZW1lQ29udGV4dCA9IC8qI19fUFVSRV9fKi9SZWFjdC5jcmVhdGVDb250ZXh0KHtcbiAgcHJlZml4ZXM6IHt9LFxuICBicmVha3BvaW50czogREVGQVVMVF9CUkVBS1BPSU5UUyxcbiAgbWluQnJlYWtwb2ludDogREVGQVVMVF9NSU5fQlJFQUtQT0lOVFxufSk7XG5jb25zdCB7XG4gIENvbnN1bWVyLFxuICBQcm92aWRlclxufSA9IFRoZW1lQ29udGV4dDtcbmZ1bmN0aW9uIFRoZW1lUHJvdmlkZXIoe1xuICBwcmVmaXhlcyA9IHt9LFxuICBicmVha3BvaW50cyA9IERFRkFVTFRfQlJFQUtQT0lOVFMsXG4gIG1pbkJyZWFrcG9pbnQgPSBERUZBVUxUX01JTl9CUkVBS1BPSU5ULFxuICBkaXIsXG4gIGNoaWxkcmVuXG59KSB7XG4gIGNvbnN0IGNvbnRleHRWYWx1ZSA9IHVzZU1lbW8oKCkgPT4gKHtcbiAgICBwcmVmaXhlczoge1xuICAgICAgLi4ucHJlZml4ZXNcbiAgICB9LFxuICAgIGJyZWFrcG9pbnRzLFxuICAgIG1pbkJyZWFrcG9pbnQsXG4gICAgZGlyXG4gIH0pLCBbcHJlZml4ZXMsIGJyZWFrcG9pbnRzLCBtaW5CcmVha3BvaW50LCBkaXJdKTtcbiAgcmV0dXJuIC8qI19fUFVSRV9fKi9fanN4KFByb3ZpZGVyLCB7XG4gICAgdmFsdWU6IGNvbnRleHRWYWx1ZSxcbiAgICBjaGlsZHJlbjogY2hpbGRyZW5cbiAgfSk7XG59XG5leHBvcnQgZnVuY3Rpb24gdXNlQm9vdHN0cmFwUHJlZml4KHByZWZpeCwgZGVmYXVsdFByZWZpeCkge1xuICBjb25zdCB7XG4gICAgcHJlZml4ZXNcbiAgfSA9IHVzZUNvbnRleHQoVGhlbWVDb250ZXh0KTtcbiAgcmV0dXJuIHByZWZpeCB8fCBwcmVmaXhlc1tkZWZhdWx0UHJlZml4XSB8fCBkZWZhdWx0UHJlZml4O1xufVxuZXhwb3J0IGZ1bmN0aW9uIHVzZUJvb3RzdHJhcEJyZWFrcG9pbnRzKCkge1xuICBjb25zdCB7XG4gICAgYnJlYWtwb2ludHNcbiAgfSA9IHVzZUNvbnRleHQoVGhlbWVDb250ZXh0KTtcbiAgcmV0dXJuIGJyZWFrcG9pbnRzO1xufVxuZXhwb3J0IGZ1bmN0aW9uIHVzZUJvb3RzdHJhcE1pbkJyZWFrcG9pbnQoKSB7XG4gIGNvbnN0IHtcbiAgICBtaW5CcmVha3BvaW50XG4gIH0gPSB1c2VDb250ZXh0KFRoZW1lQ29udGV4dCk7XG4gIHJldHVybiBtaW5CcmVha3BvaW50O1xufVxuZXhwb3J0IGZ1bmN0aW9uIHVzZUlzUlRMKCkge1xuICBjb25zdCB7XG4gICAgZGlyXG4gIH0gPSB1c2VDb250ZXh0KFRoZW1lQ29udGV4dCk7XG4gIHJldHVybiBkaXIgPT09ICdydGwnO1xufVxuZnVuY3Rpb24gY3JlYXRlQm9vdHN0cmFwQ29tcG9uZW50KENvbXBvbmVudCwgb3B0cykge1xuICBpZiAodHlwZW9mIG9wdHMgPT09ICdzdHJpbmcnKSBvcHRzID0ge1xuICAgIHByZWZpeDogb3B0c1xuICB9O1xuICBjb25zdCBpc0NsYXNzeSA9IENvbXBvbmVudC5wcm90b3R5cGUgJiYgQ29tcG9uZW50LnByb3RvdHlwZS5pc1JlYWN0Q29tcG9uZW50O1xuICAvLyBJZiBpdCdzIGEgZnVuY3Rpb25hbCBjb21wb25lbnQgbWFrZSBzdXJlIHdlIGRvbid0IGJyZWFrIGl0IHdpdGggYSByZWZcbiAgY29uc3Qge1xuICAgIHByZWZpeCxcbiAgICBmb3J3YXJkUmVmQXMgPSBpc0NsYXNzeSA/ICdyZWYnIDogJ2lubmVyUmVmJ1xuICB9ID0gb3B0cztcbiAgY29uc3QgV3JhcHBlZCA9IC8qI19fUFVSRV9fKi9SZWFjdC5mb3J3YXJkUmVmKCh7XG4gICAgLi4ucHJvcHNcbiAgfSwgcmVmKSA9PiB7XG4gICAgcHJvcHNbZm9yd2FyZFJlZkFzXSA9IHJlZjtcbiAgICBjb25zdCBic1ByZWZpeCA9IHVzZUJvb3RzdHJhcFByZWZpeChwcm9wcy5ic1ByZWZpeCwgcHJlZml4KTtcbiAgICByZXR1cm4gLyojX19QVVJFX18qL19qc3goQ29tcG9uZW50LCB7XG4gICAgICAuLi5wcm9wcyxcbiAgICAgIGJzUHJlZml4OiBic1ByZWZpeFxuICAgIH0pO1xuICB9KTtcbiAgV3JhcHBlZC5kaXNwbGF5TmFtZSA9IGBCb290c3RyYXAoJHtDb21wb25lbnQuZGlzcGxheU5hbWUgfHwgQ29tcG9uZW50Lm5hbWV9KWA7XG4gIHJldHVybiBXcmFwcGVkO1xufVxuZXhwb3J0IHsgY3JlYXRlQm9vdHN0cmFwQ29tcG9uZW50LCBDb25zdW1lciBhcyBUaGVtZUNvbnN1bWVyIH07XG5leHBvcnQgZGVmYXVsdCBUaGVtZVByb3ZpZGVyOyIsIi8qKlxuICogUmV0dXJucyB0aGUgb3duZXIgZG9jdW1lbnQgb2YgYSBnaXZlbiBlbGVtZW50LlxuICogXG4gKiBAcGFyYW0gbm9kZSB0aGUgZWxlbWVudFxuICovXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBvd25lckRvY3VtZW50KG5vZGUpIHtcbiAgcmV0dXJuIG5vZGUgJiYgbm9kZS5vd25lckRvY3VtZW50IHx8IGRvY3VtZW50O1xufSIsImltcG9ydCBvd25lckRvY3VtZW50IGZyb20gJy4vb3duZXJEb2N1bWVudCc7XG4vKipcbiAqIFJldHVybnMgdGhlIG93bmVyIHdpbmRvdyBvZiBhIGdpdmVuIGVsZW1lbnQuXG4gKiBcbiAqIEBwYXJhbSBub2RlIHRoZSBlbGVtZW50XG4gKi9cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gb3duZXJXaW5kb3cobm9kZSkge1xuICB2YXIgZG9jID0gb3duZXJEb2N1bWVudChub2RlKTtcbiAgcmV0dXJuIGRvYyAmJiBkb2MuZGVmYXVsdFZpZXcgfHwgd2luZG93O1xufSIsImltcG9ydCBvd25lcldpbmRvdyBmcm9tICcuL293bmVyV2luZG93Jztcbi8qKlxuICogUmV0dXJucyBvbmUgb3IgYWxsIGNvbXB1dGVkIHN0eWxlIHByb3BlcnRpZXMgb2YgYW4gZWxlbWVudC5cbiAqIFxuICogQHBhcmFtIG5vZGUgdGhlIGVsZW1lbnRcbiAqIEBwYXJhbSBwc3VlZG9FbGVtZW50IHRoZSBzdHlsZSBwcm9wZXJ0eVxuICovXG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIGdldENvbXB1dGVkU3R5bGUobm9kZSwgcHN1ZWRvRWxlbWVudCkge1xuICByZXR1cm4gb3duZXJXaW5kb3cobm9kZSkuZ2V0Q29tcHV0ZWRTdHlsZShub2RlLCBwc3VlZG9FbGVtZW50KTtcbn0iLCJ2YXIgclVwcGVyID0gLyhbQS1aXSkvZztcbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIGh5cGhlbmF0ZShzdHJpbmcpIHtcbiAgcmV0dXJuIHN0cmluZy5yZXBsYWNlKHJVcHBlciwgJy0kMScpLnRvTG93ZXJDYXNlKCk7XG59IiwiLyoqXG4gKiBDb3B5cmlnaHQgMjAxMy0yMDE0LCBGYWNlYm9vaywgSW5jLlxuICogQWxsIHJpZ2h0cyByZXNlcnZlZC5cbiAqIGh0dHBzOi8vZ2l0aHViLmNvbS9mYWNlYm9vay9yZWFjdC9ibG9iLzJhZWI4YTJhNmJlYjAwNjE3YTQyMTdmN2Y4Mjg0OTI0ZmEyYWQ4MTkvc3JjL3ZlbmRvci9jb3JlL2h5cGhlbmF0ZVN0eWxlTmFtZS5qc1xuICovXG5pbXBvcnQgaHlwaGVuYXRlIGZyb20gJy4vaHlwaGVuYXRlJztcbnZhciBtc1BhdHRlcm4gPSAvXm1zLS87XG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBoeXBoZW5hdGVTdHlsZU5hbWUoc3RyaW5nKSB7XG4gIHJldHVybiBoeXBoZW5hdGUoc3RyaW5nKS5yZXBsYWNlKG1zUGF0dGVybiwgJy1tcy0nKTtcbn0iLCJ2YXIgc3VwcG9ydGVkVHJhbnNmb3JtcyA9IC9eKCh0cmFuc2xhdGV8cm90YXRlfHNjYWxlKShYfFl8WnwzZCk/fG1hdHJpeCgzZCk/fHBlcnNwZWN0aXZlfHNrZXcoWHxZKT8pJC9pO1xuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gaXNUcmFuc2Zvcm0odmFsdWUpIHtcbiAgcmV0dXJuICEhKHZhbHVlICYmIHN1cHBvcnRlZFRyYW5zZm9ybXMudGVzdCh2YWx1ZSkpO1xufSIsImltcG9ydCBnZXRDb21wdXRlZFN0eWxlIGZyb20gJy4vZ2V0Q29tcHV0ZWRTdHlsZSc7XG5pbXBvcnQgaHlwaGVuYXRlIGZyb20gJy4vaHlwaGVuYXRlU3R5bGUnO1xuaW1wb3J0IGlzVHJhbnNmb3JtIGZyb20gJy4vaXNUcmFuc2Zvcm0nO1xuXG5mdW5jdGlvbiBzdHlsZShub2RlLCBwcm9wZXJ0eSkge1xuICB2YXIgY3NzID0gJyc7XG4gIHZhciB0cmFuc2Zvcm1zID0gJyc7XG5cbiAgaWYgKHR5cGVvZiBwcm9wZXJ0eSA9PT0gJ3N0cmluZycpIHtcbiAgICByZXR1cm4gbm9kZS5zdHlsZS5nZXRQcm9wZXJ0eVZhbHVlKGh5cGhlbmF0ZShwcm9wZXJ0eSkpIHx8IGdldENvbXB1dGVkU3R5bGUobm9kZSkuZ2V0UHJvcGVydHlWYWx1ZShoeXBoZW5hdGUocHJvcGVydHkpKTtcbiAgfVxuXG4gIE9iamVjdC5rZXlzKHByb3BlcnR5KS5mb3JFYWNoKGZ1bmN0aW9uIChrZXkpIHtcbiAgICB2YXIgdmFsdWUgPSBwcm9wZXJ0eVtrZXldO1xuXG4gICAgaWYgKCF2YWx1ZSAmJiB2YWx1ZSAhPT0gMCkge1xuICAgICAgbm9kZS5zdHlsZS5yZW1vdmVQcm9wZXJ0eShoeXBoZW5hdGUoa2V5KSk7XG4gICAgfSBlbHNlIGlmIChpc1RyYW5zZm9ybShrZXkpKSB7XG4gICAgICB0cmFuc2Zvcm1zICs9IGtleSArIFwiKFwiICsgdmFsdWUgKyBcIikgXCI7XG4gICAgfSBlbHNlIHtcbiAgICAgIGNzcyArPSBoeXBoZW5hdGUoa2V5KSArIFwiOiBcIiArIHZhbHVlICsgXCI7XCI7XG4gICAgfVxuICB9KTtcblxuICBpZiAodHJhbnNmb3Jtcykge1xuICAgIGNzcyArPSBcInRyYW5zZm9ybTogXCIgKyB0cmFuc2Zvcm1zICsgXCI7XCI7XG4gIH1cblxuICBub2RlLnN0eWxlLmNzc1RleHQgKz0gXCI7XCIgKyBjc3M7XG59XG5cbmV4cG9ydCBkZWZhdWx0IHN0eWxlOyIsIi8qKiBAbGljZW5zZSBSZWFjdCB2MTYuMTMuMVxuICogcmVhY3QtaXMuZGV2ZWxvcG1lbnQuanNcbiAqXG4gKiBDb3B5cmlnaHQgKGMpIEZhY2Vib29rLCBJbmMuIGFuZCBpdHMgYWZmaWxpYXRlcy5cbiAqXG4gKiBUaGlzIHNvdXJjZSBjb2RlIGlzIGxpY2Vuc2VkIHVuZGVyIHRoZSBNSVQgbGljZW5zZSBmb3VuZCBpbiB0aGVcbiAqIExJQ0VOU0UgZmlsZSBpbiB0aGUgcm9vdCBkaXJlY3Rvcnkgb2YgdGhpcyBzb3VyY2UgdHJlZS5cbiAqL1xuXG4ndXNlIHN0cmljdCc7XG5cblxuXG5pZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09IFwicHJvZHVjdGlvblwiKSB7XG4gIChmdW5jdGlvbigpIHtcbid1c2Ugc3RyaWN0JztcblxuLy8gVGhlIFN5bWJvbCB1c2VkIHRvIHRhZyB0aGUgUmVhY3RFbGVtZW50LWxpa2UgdHlwZXMuIElmIHRoZXJlIGlzIG5vIG5hdGl2ZSBTeW1ib2xcbi8vIG5vciBwb2x5ZmlsbCwgdGhlbiBhIHBsYWluIG51bWJlciBpcyB1c2VkIGZvciBwZXJmb3JtYW5jZS5cbnZhciBoYXNTeW1ib2wgPSB0eXBlb2YgU3ltYm9sID09PSAnZnVuY3Rpb24nICYmIFN5bWJvbC5mb3I7XG52YXIgUkVBQ1RfRUxFTUVOVF9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QuZWxlbWVudCcpIDogMHhlYWM3O1xudmFyIFJFQUNUX1BPUlRBTF9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QucG9ydGFsJykgOiAweGVhY2E7XG52YXIgUkVBQ1RfRlJBR01FTlRfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmZyYWdtZW50JykgOiAweGVhY2I7XG52YXIgUkVBQ1RfU1RSSUNUX01PREVfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LnN0cmljdF9tb2RlJykgOiAweGVhY2M7XG52YXIgUkVBQ1RfUFJPRklMRVJfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LnByb2ZpbGVyJykgOiAweGVhZDI7XG52YXIgUkVBQ1RfUFJPVklERVJfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LnByb3ZpZGVyJykgOiAweGVhY2Q7XG52YXIgUkVBQ1RfQ09OVEVYVF9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QuY29udGV4dCcpIDogMHhlYWNlOyAvLyBUT0RPOiBXZSBkb24ndCB1c2UgQXN5bmNNb2RlIG9yIENvbmN1cnJlbnRNb2RlIGFueW1vcmUuIFRoZXkgd2VyZSB0ZW1wb3Jhcnlcbi8vICh1bnN0YWJsZSkgQVBJcyB0aGF0IGhhdmUgYmVlbiByZW1vdmVkLiBDYW4gd2UgcmVtb3ZlIHRoZSBzeW1ib2xzP1xuXG52YXIgUkVBQ1RfQVNZTkNfTU9ERV9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QuYXN5bmNfbW9kZScpIDogMHhlYWNmO1xudmFyIFJFQUNUX0NPTkNVUlJFTlRfTU9ERV9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QuY29uY3VycmVudF9tb2RlJykgOiAweGVhY2Y7XG52YXIgUkVBQ1RfRk9SV0FSRF9SRUZfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmZvcndhcmRfcmVmJykgOiAweGVhZDA7XG52YXIgUkVBQ1RfU1VTUEVOU0VfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LnN1c3BlbnNlJykgOiAweGVhZDE7XG52YXIgUkVBQ1RfU1VTUEVOU0VfTElTVF9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3Quc3VzcGVuc2VfbGlzdCcpIDogMHhlYWQ4O1xudmFyIFJFQUNUX01FTU9fVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0Lm1lbW8nKSA6IDB4ZWFkMztcbnZhciBSRUFDVF9MQVpZX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5sYXp5JykgOiAweGVhZDQ7XG52YXIgUkVBQ1RfQkxPQ0tfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmJsb2NrJykgOiAweGVhZDk7XG52YXIgUkVBQ1RfRlVOREFNRU5UQUxfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmZ1bmRhbWVudGFsJykgOiAweGVhZDU7XG52YXIgUkVBQ1RfUkVTUE9OREVSX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5yZXNwb25kZXInKSA6IDB4ZWFkNjtcbnZhciBSRUFDVF9TQ09QRV9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3Quc2NvcGUnKSA6IDB4ZWFkNztcblxuZnVuY3Rpb24gaXNWYWxpZEVsZW1lbnRUeXBlKHR5cGUpIHtcbiAgcmV0dXJuIHR5cGVvZiB0eXBlID09PSAnc3RyaW5nJyB8fCB0eXBlb2YgdHlwZSA9PT0gJ2Z1bmN0aW9uJyB8fCAvLyBOb3RlOiBpdHMgdHlwZW9mIG1pZ2h0IGJlIG90aGVyIHRoYW4gJ3N5bWJvbCcgb3IgJ251bWJlcicgaWYgaXQncyBhIHBvbHlmaWxsLlxuICB0eXBlID09PSBSRUFDVF9GUkFHTUVOVF9UWVBFIHx8IHR5cGUgPT09IFJFQUNUX0NPTkNVUlJFTlRfTU9ERV9UWVBFIHx8IHR5cGUgPT09IFJFQUNUX1BST0ZJTEVSX1RZUEUgfHwgdHlwZSA9PT0gUkVBQ1RfU1RSSUNUX01PREVfVFlQRSB8fCB0eXBlID09PSBSRUFDVF9TVVNQRU5TRV9UWVBFIHx8IHR5cGUgPT09IFJFQUNUX1NVU1BFTlNFX0xJU1RfVFlQRSB8fCB0eXBlb2YgdHlwZSA9PT0gJ29iamVjdCcgJiYgdHlwZSAhPT0gbnVsbCAmJiAodHlwZS4kJHR5cGVvZiA9PT0gUkVBQ1RfTEFaWV9UWVBFIHx8IHR5cGUuJCR0eXBlb2YgPT09IFJFQUNUX01FTU9fVFlQRSB8fCB0eXBlLiQkdHlwZW9mID09PSBSRUFDVF9QUk9WSURFUl9UWVBFIHx8IHR5cGUuJCR0eXBlb2YgPT09IFJFQUNUX0NPTlRFWFRfVFlQRSB8fCB0eXBlLiQkdHlwZW9mID09PSBSRUFDVF9GT1JXQVJEX1JFRl9UWVBFIHx8IHR5cGUuJCR0eXBlb2YgPT09IFJFQUNUX0ZVTkRBTUVOVEFMX1RZUEUgfHwgdHlwZS4kJHR5cGVvZiA9PT0gUkVBQ1RfUkVTUE9OREVSX1RZUEUgfHwgdHlwZS4kJHR5cGVvZiA9PT0gUkVBQ1RfU0NPUEVfVFlQRSB8fCB0eXBlLiQkdHlwZW9mID09PSBSRUFDVF9CTE9DS19UWVBFKTtcbn1cblxuZnVuY3Rpb24gdHlwZU9mKG9iamVjdCkge1xuICBpZiAodHlwZW9mIG9iamVjdCA9PT0gJ29iamVjdCcgJiYgb2JqZWN0ICE9PSBudWxsKSB7XG4gICAgdmFyICQkdHlwZW9mID0gb2JqZWN0LiQkdHlwZW9mO1xuXG4gICAgc3dpdGNoICgkJHR5cGVvZikge1xuICAgICAgY2FzZSBSRUFDVF9FTEVNRU5UX1RZUEU6XG4gICAgICAgIHZhciB0eXBlID0gb2JqZWN0LnR5cGU7XG5cbiAgICAgICAgc3dpdGNoICh0eXBlKSB7XG4gICAgICAgICAgY2FzZSBSRUFDVF9BU1lOQ19NT0RFX1RZUEU6XG4gICAgICAgICAgY2FzZSBSRUFDVF9DT05DVVJSRU5UX01PREVfVFlQRTpcbiAgICAgICAgICBjYXNlIFJFQUNUX0ZSQUdNRU5UX1RZUEU6XG4gICAgICAgICAgY2FzZSBSRUFDVF9QUk9GSUxFUl9UWVBFOlxuICAgICAgICAgIGNhc2UgUkVBQ1RfU1RSSUNUX01PREVfVFlQRTpcbiAgICAgICAgICBjYXNlIFJFQUNUX1NVU1BFTlNFX1RZUEU6XG4gICAgICAgICAgICByZXR1cm4gdHlwZTtcblxuICAgICAgICAgIGRlZmF1bHQ6XG4gICAgICAgICAgICB2YXIgJCR0eXBlb2ZUeXBlID0gdHlwZSAmJiB0eXBlLiQkdHlwZW9mO1xuXG4gICAgICAgICAgICBzd2l0Y2ggKCQkdHlwZW9mVHlwZSkge1xuICAgICAgICAgICAgICBjYXNlIFJFQUNUX0NPTlRFWFRfVFlQRTpcbiAgICAgICAgICAgICAgY2FzZSBSRUFDVF9GT1JXQVJEX1JFRl9UWVBFOlxuICAgICAgICAgICAgICBjYXNlIFJFQUNUX0xBWllfVFlQRTpcbiAgICAgICAgICAgICAgY2FzZSBSRUFDVF9NRU1PX1RZUEU6XG4gICAgICAgICAgICAgIGNhc2UgUkVBQ1RfUFJPVklERVJfVFlQRTpcbiAgICAgICAgICAgICAgICByZXR1cm4gJCR0eXBlb2ZUeXBlO1xuXG4gICAgICAgICAgICAgIGRlZmF1bHQ6XG4gICAgICAgICAgICAgICAgcmV0dXJuICQkdHlwZW9mO1xuICAgICAgICAgICAgfVxuXG4gICAgICAgIH1cblxuICAgICAgY2FzZSBSRUFDVF9QT1JUQUxfVFlQRTpcbiAgICAgICAgcmV0dXJuICQkdHlwZW9mO1xuICAgIH1cbiAgfVxuXG4gIHJldHVybiB1bmRlZmluZWQ7XG59IC8vIEFzeW5jTW9kZSBpcyBkZXByZWNhdGVkIGFsb25nIHdpdGggaXNBc3luY01vZGVcblxudmFyIEFzeW5jTW9kZSA9IFJFQUNUX0FTWU5DX01PREVfVFlQRTtcbnZhciBDb25jdXJyZW50TW9kZSA9IFJFQUNUX0NPTkNVUlJFTlRfTU9ERV9UWVBFO1xudmFyIENvbnRleHRDb25zdW1lciA9IFJFQUNUX0NPTlRFWFRfVFlQRTtcbnZhciBDb250ZXh0UHJvdmlkZXIgPSBSRUFDVF9QUk9WSURFUl9UWVBFO1xudmFyIEVsZW1lbnQgPSBSRUFDVF9FTEVNRU5UX1RZUEU7XG52YXIgRm9yd2FyZFJlZiA9IFJFQUNUX0ZPUldBUkRfUkVGX1RZUEU7XG52YXIgRnJhZ21lbnQgPSBSRUFDVF9GUkFHTUVOVF9UWVBFO1xudmFyIExhenkgPSBSRUFDVF9MQVpZX1RZUEU7XG52YXIgTWVtbyA9IFJFQUNUX01FTU9fVFlQRTtcbnZhciBQb3J0YWwgPSBSRUFDVF9QT1JUQUxfVFlQRTtcbnZhciBQcm9maWxlciA9IFJFQUNUX1BST0ZJTEVSX1RZUEU7XG52YXIgU3RyaWN0TW9kZSA9IFJFQUNUX1NUUklDVF9NT0RFX1RZUEU7XG52YXIgU3VzcGVuc2UgPSBSRUFDVF9TVVNQRU5TRV9UWVBFO1xudmFyIGhhc1dhcm5lZEFib3V0RGVwcmVjYXRlZElzQXN5bmNNb2RlID0gZmFsc2U7IC8vIEFzeW5jTW9kZSBzaG91bGQgYmUgZGVwcmVjYXRlZFxuXG5mdW5jdGlvbiBpc0FzeW5jTW9kZShvYmplY3QpIHtcbiAge1xuICAgIGlmICghaGFzV2FybmVkQWJvdXREZXByZWNhdGVkSXNBc3luY01vZGUpIHtcbiAgICAgIGhhc1dhcm5lZEFib3V0RGVwcmVjYXRlZElzQXN5bmNNb2RlID0gdHJ1ZTsgLy8gVXNpbmcgY29uc29sZVsnd2FybiddIHRvIGV2YWRlIEJhYmVsIGFuZCBFU0xpbnRcblxuICAgICAgY29uc29sZVsnd2FybiddKCdUaGUgUmVhY3RJcy5pc0FzeW5jTW9kZSgpIGFsaWFzIGhhcyBiZWVuIGRlcHJlY2F0ZWQsICcgKyAnYW5kIHdpbGwgYmUgcmVtb3ZlZCBpbiBSZWFjdCAxNysuIFVwZGF0ZSB5b3VyIGNvZGUgdG8gdXNlICcgKyAnUmVhY3RJcy5pc0NvbmN1cnJlbnRNb2RlKCkgaW5zdGVhZC4gSXQgaGFzIHRoZSBleGFjdCBzYW1lIEFQSS4nKTtcbiAgICB9XG4gIH1cblxuICByZXR1cm4gaXNDb25jdXJyZW50TW9kZShvYmplY3QpIHx8IHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9BU1lOQ19NT0RFX1RZUEU7XG59XG5mdW5jdGlvbiBpc0NvbmN1cnJlbnRNb2RlKG9iamVjdCkge1xuICByZXR1cm4gdHlwZU9mKG9iamVjdCkgPT09IFJFQUNUX0NPTkNVUlJFTlRfTU9ERV9UWVBFO1xufVxuZnVuY3Rpb24gaXNDb250ZXh0Q29uc3VtZXIob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfQ09OVEVYVF9UWVBFO1xufVxuZnVuY3Rpb24gaXNDb250ZXh0UHJvdmlkZXIob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfUFJPVklERVJfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzRWxlbWVudChvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVvZiBvYmplY3QgPT09ICdvYmplY3QnICYmIG9iamVjdCAhPT0gbnVsbCAmJiBvYmplY3QuJCR0eXBlb2YgPT09IFJFQUNUX0VMRU1FTlRfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzRm9yd2FyZFJlZihvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9GT1JXQVJEX1JFRl9UWVBFO1xufVxuZnVuY3Rpb24gaXNGcmFnbWVudChvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9GUkFHTUVOVF9UWVBFO1xufVxuZnVuY3Rpb24gaXNMYXp5KG9iamVjdCkge1xuICByZXR1cm4gdHlwZU9mKG9iamVjdCkgPT09IFJFQUNUX0xBWllfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzTWVtbyhvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9NRU1PX1RZUEU7XG59XG5mdW5jdGlvbiBpc1BvcnRhbChvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9QT1JUQUxfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzUHJvZmlsZXIob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfUFJPRklMRVJfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzU3RyaWN0TW9kZShvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9TVFJJQ1RfTU9ERV9UWVBFO1xufVxuZnVuY3Rpb24gaXNTdXNwZW5zZShvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9TVVNQRU5TRV9UWVBFO1xufVxuXG5leHBvcnRzLkFzeW5jTW9kZSA9IEFzeW5jTW9kZTtcbmV4cG9ydHMuQ29uY3VycmVudE1vZGUgPSBDb25jdXJyZW50TW9kZTtcbmV4cG9ydHMuQ29udGV4dENvbnN1bWVyID0gQ29udGV4dENvbnN1bWVyO1xuZXhwb3J0cy5Db250ZXh0UHJvdmlkZXIgPSBDb250ZXh0UHJvdmlkZXI7XG5leHBvcnRzLkVsZW1lbnQgPSBFbGVtZW50O1xuZXhwb3J0cy5Gb3J3YXJkUmVmID0gRm9yd2FyZFJlZjtcbmV4cG9ydHMuRnJhZ21lbnQgPSBGcmFnbWVudDtcbmV4cG9ydHMuTGF6eSA9IExhenk7XG5leHBvcnRzLk1lbW8gPSBNZW1vO1xuZXhwb3J0cy5Qb3J0YWwgPSBQb3J0YWw7XG5leHBvcnRzLlByb2ZpbGVyID0gUHJvZmlsZXI7XG5leHBvcnRzLlN0cmljdE1vZGUgPSBTdHJpY3RNb2RlO1xuZXhwb3J0cy5TdXNwZW5zZSA9IFN1c3BlbnNlO1xuZXhwb3J0cy5pc0FzeW5jTW9kZSA9IGlzQXN5bmNNb2RlO1xuZXhwb3J0cy5pc0NvbmN1cnJlbnRNb2RlID0gaXNDb25jdXJyZW50TW9kZTtcbmV4cG9ydHMuaXNDb250ZXh0Q29uc3VtZXIgPSBpc0NvbnRleHRDb25zdW1lcjtcbmV4cG9ydHMuaXNDb250ZXh0UHJvdmlkZXIgPSBpc0NvbnRleHRQcm92aWRlcjtcbmV4cG9ydHMuaXNFbGVtZW50ID0gaXNFbGVtZW50O1xuZXhwb3J0cy5pc0ZvcndhcmRSZWYgPSBpc0ZvcndhcmRSZWY7XG5leHBvcnRzLmlzRnJhZ21lbnQgPSBpc0ZyYWdtZW50O1xuZXhwb3J0cy5pc0xhenkgPSBpc0xhenk7XG5leHBvcnRzLmlzTWVtbyA9IGlzTWVtbztcbmV4cG9ydHMuaXNQb3J0YWwgPSBpc1BvcnRhbDtcbmV4cG9ydHMuaXNQcm9maWxlciA9IGlzUHJvZmlsZXI7XG5leHBvcnRzLmlzU3RyaWN0TW9kZSA9IGlzU3RyaWN0TW9kZTtcbmV4cG9ydHMuaXNTdXNwZW5zZSA9IGlzU3VzcGVuc2U7XG5leHBvcnRzLmlzVmFsaWRFbGVtZW50VHlwZSA9IGlzVmFsaWRFbGVtZW50VHlwZTtcbmV4cG9ydHMudHlwZU9mID0gdHlwZU9mO1xuICB9KSgpO1xufVxuIiwiJ3VzZSBzdHJpY3QnO1xuXG5pZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgPT09ICdwcm9kdWN0aW9uJykge1xuICBtb2R1bGUuZXhwb3J0cyA9IHJlcXVpcmUoJy4vY2pzL3JlYWN0LWlzLnByb2R1Y3Rpb24ubWluLmpzJyk7XG59IGVsc2Uge1xuICBtb2R1bGUuZXhwb3J0cyA9IHJlcXVpcmUoJy4vY2pzL3JlYWN0LWlzLmRldmVsb3BtZW50LmpzJyk7XG59XG4iLCIvKlxub2JqZWN0LWFzc2lnblxuKGMpIFNpbmRyZSBTb3JodXNcbkBsaWNlbnNlIE1JVFxuKi9cblxuJ3VzZSBzdHJpY3QnO1xuLyogZXNsaW50LWRpc2FibGUgbm8tdW51c2VkLXZhcnMgKi9cbnZhciBnZXRPd25Qcm9wZXJ0eVN5bWJvbHMgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlTeW1ib2xzO1xudmFyIGhhc093blByb3BlcnR5ID0gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eTtcbnZhciBwcm9wSXNFbnVtZXJhYmxlID0gT2JqZWN0LnByb3RvdHlwZS5wcm9wZXJ0eUlzRW51bWVyYWJsZTtcblxuZnVuY3Rpb24gdG9PYmplY3QodmFsKSB7XG5cdGlmICh2YWwgPT09IG51bGwgfHwgdmFsID09PSB1bmRlZmluZWQpIHtcblx0XHR0aHJvdyBuZXcgVHlwZUVycm9yKCdPYmplY3QuYXNzaWduIGNhbm5vdCBiZSBjYWxsZWQgd2l0aCBudWxsIG9yIHVuZGVmaW5lZCcpO1xuXHR9XG5cblx0cmV0dXJuIE9iamVjdCh2YWwpO1xufVxuXG5mdW5jdGlvbiBzaG91bGRVc2VOYXRpdmUoKSB7XG5cdHRyeSB7XG5cdFx0aWYgKCFPYmplY3QuYXNzaWduKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Ly8gRGV0ZWN0IGJ1Z2d5IHByb3BlcnR5IGVudW1lcmF0aW9uIG9yZGVyIGluIG9sZGVyIFY4IHZlcnNpb25zLlxuXG5cdFx0Ly8gaHR0cHM6Ly9idWdzLmNocm9taXVtLm9yZy9wL3Y4L2lzc3Vlcy9kZXRhaWw/aWQ9NDExOFxuXHRcdHZhciB0ZXN0MSA9IG5ldyBTdHJpbmcoJ2FiYycpOyAgLy8gZXNsaW50LWRpc2FibGUtbGluZSBuby1uZXctd3JhcHBlcnNcblx0XHR0ZXN0MVs1XSA9ICdkZSc7XG5cdFx0aWYgKE9iamVjdC5nZXRPd25Qcm9wZXJ0eU5hbWVzKHRlc3QxKVswXSA9PT0gJzUnKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Ly8gaHR0cHM6Ly9idWdzLmNocm9taXVtLm9yZy9wL3Y4L2lzc3Vlcy9kZXRhaWw/aWQ9MzA1NlxuXHRcdHZhciB0ZXN0MiA9IHt9O1xuXHRcdGZvciAodmFyIGkgPSAwOyBpIDwgMTA7IGkrKykge1xuXHRcdFx0dGVzdDJbJ18nICsgU3RyaW5nLmZyb21DaGFyQ29kZShpKV0gPSBpO1xuXHRcdH1cblx0XHR2YXIgb3JkZXIyID0gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXModGVzdDIpLm1hcChmdW5jdGlvbiAobikge1xuXHRcdFx0cmV0dXJuIHRlc3QyW25dO1xuXHRcdH0pO1xuXHRcdGlmIChvcmRlcjIuam9pbignJykgIT09ICcwMTIzNDU2Nzg5Jykge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdC8vIGh0dHBzOi8vYnVncy5jaHJvbWl1bS5vcmcvcC92OC9pc3N1ZXMvZGV0YWlsP2lkPTMwNTZcblx0XHR2YXIgdGVzdDMgPSB7fTtcblx0XHQnYWJjZGVmZ2hpamtsbW5vcHFyc3QnLnNwbGl0KCcnKS5mb3JFYWNoKGZ1bmN0aW9uIChsZXR0ZXIpIHtcblx0XHRcdHRlc3QzW2xldHRlcl0gPSBsZXR0ZXI7XG5cdFx0fSk7XG5cdFx0aWYgKE9iamVjdC5rZXlzKE9iamVjdC5hc3NpZ24oe30sIHRlc3QzKSkuam9pbignJykgIT09XG5cdFx0XHRcdCdhYmNkZWZnaGlqa2xtbm9wcXJzdCcpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cblx0XHRyZXR1cm4gdHJ1ZTtcblx0fSBjYXRjaCAoZXJyKSB7XG5cdFx0Ly8gV2UgZG9uJ3QgZXhwZWN0IGFueSBvZiB0aGUgYWJvdmUgdG8gdGhyb3csIGJ1dCBiZXR0ZXIgdG8gYmUgc2FmZS5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cbn1cblxubW9kdWxlLmV4cG9ydHMgPSBzaG91bGRVc2VOYXRpdmUoKSA/IE9iamVjdC5hc3NpZ24gOiBmdW5jdGlvbiAodGFyZ2V0LCBzb3VyY2UpIHtcblx0dmFyIGZyb207XG5cdHZhciB0byA9IHRvT2JqZWN0KHRhcmdldCk7XG5cdHZhciBzeW1ib2xzO1xuXG5cdGZvciAodmFyIHMgPSAxOyBzIDwgYXJndW1lbnRzLmxlbmd0aDsgcysrKSB7XG5cdFx0ZnJvbSA9IE9iamVjdChhcmd1bWVudHNbc10pO1xuXG5cdFx0Zm9yICh2YXIga2V5IGluIGZyb20pIHtcblx0XHRcdGlmIChoYXNPd25Qcm9wZXJ0eS5jYWxsKGZyb20sIGtleSkpIHtcblx0XHRcdFx0dG9ba2V5XSA9IGZyb21ba2V5XTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRpZiAoZ2V0T3duUHJvcGVydHlTeW1ib2xzKSB7XG5cdFx0XHRzeW1ib2xzID0gZ2V0T3duUHJvcGVydHlTeW1ib2xzKGZyb20pO1xuXHRcdFx0Zm9yICh2YXIgaSA9IDA7IGkgPCBzeW1ib2xzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRcdGlmIChwcm9wSXNFbnVtZXJhYmxlLmNhbGwoZnJvbSwgc3ltYm9sc1tpXSkpIHtcblx0XHRcdFx0XHR0b1tzeW1ib2xzW2ldXSA9IGZyb21bc3ltYm9sc1tpXV07XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gdG87XG59O1xuIiwiLyoqXG4gKiBDb3B5cmlnaHQgKGMpIDIwMTMtcHJlc2VudCwgRmFjZWJvb2ssIEluYy5cbiAqXG4gKiBUaGlzIHNvdXJjZSBjb2RlIGlzIGxpY2Vuc2VkIHVuZGVyIHRoZSBNSVQgbGljZW5zZSBmb3VuZCBpbiB0aGVcbiAqIExJQ0VOU0UgZmlsZSBpbiB0aGUgcm9vdCBkaXJlY3Rvcnkgb2YgdGhpcyBzb3VyY2UgdHJlZS5cbiAqL1xuXG4ndXNlIHN0cmljdCc7XG5cbnZhciBSZWFjdFByb3BUeXBlc1NlY3JldCA9ICdTRUNSRVRfRE9fTk9UX1BBU1NfVEhJU19PUl9ZT1VfV0lMTF9CRV9GSVJFRCc7XG5cbm1vZHVsZS5leHBvcnRzID0gUmVhY3RQcm9wVHlwZXNTZWNyZXQ7XG4iLCJtb2R1bGUuZXhwb3J0cyA9IEZ1bmN0aW9uLmNhbGwuYmluZChPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5KTtcbiIsIi8qKlxuICogQ29weXJpZ2h0IChjKSAyMDEzLXByZXNlbnQsIEZhY2Vib29rLCBJbmMuXG4gKlxuICogVGhpcyBzb3VyY2UgY29kZSBpcyBsaWNlbnNlZCB1bmRlciB0aGUgTUlUIGxpY2Vuc2UgZm91bmQgaW4gdGhlXG4gKiBMSUNFTlNFIGZpbGUgaW4gdGhlIHJvb3QgZGlyZWN0b3J5IG9mIHRoaXMgc291cmNlIHRyZWUuXG4gKi9cblxuJ3VzZSBzdHJpY3QnO1xuXG52YXIgcHJpbnRXYXJuaW5nID0gZnVuY3Rpb24oKSB7fTtcblxuaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicpIHtcbiAgdmFyIFJlYWN0UHJvcFR5cGVzU2VjcmV0ID0gcmVxdWlyZSgnLi9saWIvUmVhY3RQcm9wVHlwZXNTZWNyZXQnKTtcbiAgdmFyIGxvZ2dlZFR5cGVGYWlsdXJlcyA9IHt9O1xuICB2YXIgaGFzID0gcmVxdWlyZSgnLi9saWIvaGFzJyk7XG5cbiAgcHJpbnRXYXJuaW5nID0gZnVuY3Rpb24odGV4dCkge1xuICAgIHZhciBtZXNzYWdlID0gJ1dhcm5pbmc6ICcgKyB0ZXh0O1xuICAgIGlmICh0eXBlb2YgY29uc29sZSAhPT0gJ3VuZGVmaW5lZCcpIHtcbiAgICAgIGNvbnNvbGUuZXJyb3IobWVzc2FnZSk7XG4gICAgfVxuICAgIHRyeSB7XG4gICAgICAvLyAtLS0gV2VsY29tZSB0byBkZWJ1Z2dpbmcgUmVhY3QgLS0tXG4gICAgICAvLyBUaGlzIGVycm9yIHdhcyB0aHJvd24gYXMgYSBjb252ZW5pZW5jZSBzbyB0aGF0IHlvdSBjYW4gdXNlIHRoaXMgc3RhY2tcbiAgICAgIC8vIHRvIGZpbmQgdGhlIGNhbGxzaXRlIHRoYXQgY2F1c2VkIHRoaXMgd2FybmluZyB0byBmaXJlLlxuICAgICAgdGhyb3cgbmV3IEVycm9yKG1lc3NhZ2UpO1xuICAgIH0gY2F0Y2ggKHgpIHsgLyoqLyB9XG4gIH07XG59XG5cbi8qKlxuICogQXNzZXJ0IHRoYXQgdGhlIHZhbHVlcyBtYXRjaCB3aXRoIHRoZSB0eXBlIHNwZWNzLlxuICogRXJyb3IgbWVzc2FnZXMgYXJlIG1lbW9yaXplZCBhbmQgd2lsbCBvbmx5IGJlIHNob3duIG9uY2UuXG4gKlxuICogQHBhcmFtIHtvYmplY3R9IHR5cGVTcGVjcyBNYXAgb2YgbmFtZSB0byBhIFJlYWN0UHJvcFR5cGVcbiAqIEBwYXJhbSB7b2JqZWN0fSB2YWx1ZXMgUnVudGltZSB2YWx1ZXMgdGhhdCBuZWVkIHRvIGJlIHR5cGUtY2hlY2tlZFxuICogQHBhcmFtIHtzdHJpbmd9IGxvY2F0aW9uIGUuZy4gXCJwcm9wXCIsIFwiY29udGV4dFwiLCBcImNoaWxkIGNvbnRleHRcIlxuICogQHBhcmFtIHtzdHJpbmd9IGNvbXBvbmVudE5hbWUgTmFtZSBvZiB0aGUgY29tcG9uZW50IGZvciBlcnJvciBtZXNzYWdlcy5cbiAqIEBwYXJhbSB7P0Z1bmN0aW9ufSBnZXRTdGFjayBSZXR1cm5zIHRoZSBjb21wb25lbnQgc3RhY2suXG4gKiBAcHJpdmF0ZVxuICovXG5mdW5jdGlvbiBjaGVja1Byb3BUeXBlcyh0eXBlU3BlY3MsIHZhbHVlcywgbG9jYXRpb24sIGNvbXBvbmVudE5hbWUsIGdldFN0YWNrKSB7XG4gIGlmIChwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gJ3Byb2R1Y3Rpb24nKSB7XG4gICAgZm9yICh2YXIgdHlwZVNwZWNOYW1lIGluIHR5cGVTcGVjcykge1xuICAgICAgaWYgKGhhcyh0eXBlU3BlY3MsIHR5cGVTcGVjTmFtZSkpIHtcbiAgICAgICAgdmFyIGVycm9yO1xuICAgICAgICAvLyBQcm9wIHR5cGUgdmFsaWRhdGlvbiBtYXkgdGhyb3cuIEluIGNhc2UgdGhleSBkbywgd2UgZG9uJ3Qgd2FudCB0b1xuICAgICAgICAvLyBmYWlsIHRoZSByZW5kZXIgcGhhc2Ugd2hlcmUgaXQgZGlkbid0IGZhaWwgYmVmb3JlLiBTbyB3ZSBsb2cgaXQuXG4gICAgICAgIC8vIEFmdGVyIHRoZXNlIGhhdmUgYmVlbiBjbGVhbmVkIHVwLCB3ZSdsbCBsZXQgdGhlbSB0aHJvdy5cbiAgICAgICAgdHJ5IHtcbiAgICAgICAgICAvLyBUaGlzIGlzIGludGVudGlvbmFsbHkgYW4gaW52YXJpYW50IHRoYXQgZ2V0cyBjYXVnaHQuIEl0J3MgdGhlIHNhbWVcbiAgICAgICAgICAvLyBiZWhhdmlvciBhcyB3aXRob3V0IHRoaXMgc3RhdGVtZW50IGV4Y2VwdCB3aXRoIGEgYmV0dGVyIG1lc3NhZ2UuXG4gICAgICAgICAgaWYgKHR5cGVvZiB0eXBlU3BlY3NbdHlwZVNwZWNOYW1lXSAhPT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICAgICAgdmFyIGVyciA9IEVycm9yKFxuICAgICAgICAgICAgICAoY29tcG9uZW50TmFtZSB8fCAnUmVhY3QgY2xhc3MnKSArICc6ICcgKyBsb2NhdGlvbiArICcgdHlwZSBgJyArIHR5cGVTcGVjTmFtZSArICdgIGlzIGludmFsaWQ7ICcgK1xuICAgICAgICAgICAgICAnaXQgbXVzdCBiZSBhIGZ1bmN0aW9uLCB1c3VhbGx5IGZyb20gdGhlIGBwcm9wLXR5cGVzYCBwYWNrYWdlLCBidXQgcmVjZWl2ZWQgYCcgKyB0eXBlb2YgdHlwZVNwZWNzW3R5cGVTcGVjTmFtZV0gKyAnYC4nICtcbiAgICAgICAgICAgICAgJ1RoaXMgb2Z0ZW4gaGFwcGVucyBiZWNhdXNlIG9mIHR5cG9zIHN1Y2ggYXMgYFByb3BUeXBlcy5mdW5jdGlvbmAgaW5zdGVhZCBvZiBgUHJvcFR5cGVzLmZ1bmNgLidcbiAgICAgICAgICAgICk7XG4gICAgICAgICAgICBlcnIubmFtZSA9ICdJbnZhcmlhbnQgVmlvbGF0aW9uJztcbiAgICAgICAgICAgIHRocm93IGVycjtcbiAgICAgICAgICB9XG4gICAgICAgICAgZXJyb3IgPSB0eXBlU3BlY3NbdHlwZVNwZWNOYW1lXSh2YWx1ZXMsIHR5cGVTcGVjTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIG51bGwsIFJlYWN0UHJvcFR5cGVzU2VjcmV0KTtcbiAgICAgICAgfSBjYXRjaCAoZXgpIHtcbiAgICAgICAgICBlcnJvciA9IGV4O1xuICAgICAgICB9XG4gICAgICAgIGlmIChlcnJvciAmJiAhKGVycm9yIGluc3RhbmNlb2YgRXJyb3IpKSB7XG4gICAgICAgICAgcHJpbnRXYXJuaW5nKFxuICAgICAgICAgICAgKGNvbXBvbmVudE5hbWUgfHwgJ1JlYWN0IGNsYXNzJykgKyAnOiB0eXBlIHNwZWNpZmljYXRpb24gb2YgJyArXG4gICAgICAgICAgICBsb2NhdGlvbiArICcgYCcgKyB0eXBlU3BlY05hbWUgKyAnYCBpcyBpbnZhbGlkOyB0aGUgdHlwZSBjaGVja2VyICcgK1xuICAgICAgICAgICAgJ2Z1bmN0aW9uIG11c3QgcmV0dXJuIGBudWxsYCBvciBhbiBgRXJyb3JgIGJ1dCByZXR1cm5lZCBhICcgKyB0eXBlb2YgZXJyb3IgKyAnLiAnICtcbiAgICAgICAgICAgICdZb3UgbWF5IGhhdmUgZm9yZ290dGVuIHRvIHBhc3MgYW4gYXJndW1lbnQgdG8gdGhlIHR5cGUgY2hlY2tlciAnICtcbiAgICAgICAgICAgICdjcmVhdG9yIChhcnJheU9mLCBpbnN0YW5jZU9mLCBvYmplY3RPZiwgb25lT2YsIG9uZU9mVHlwZSwgYW5kICcgK1xuICAgICAgICAgICAgJ3NoYXBlIGFsbCByZXF1aXJlIGFuIGFyZ3VtZW50KS4nXG4gICAgICAgICAgKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoZXJyb3IgaW5zdGFuY2VvZiBFcnJvciAmJiAhKGVycm9yLm1lc3NhZ2UgaW4gbG9nZ2VkVHlwZUZhaWx1cmVzKSkge1xuICAgICAgICAgIC8vIE9ubHkgbW9uaXRvciB0aGlzIGZhaWx1cmUgb25jZSBiZWNhdXNlIHRoZXJlIHRlbmRzIHRvIGJlIGEgbG90IG9mIHRoZVxuICAgICAgICAgIC8vIHNhbWUgZXJyb3IuXG4gICAgICAgICAgbG9nZ2VkVHlwZUZhaWx1cmVzW2Vycm9yLm1lc3NhZ2VdID0gdHJ1ZTtcblxuICAgICAgICAgIHZhciBzdGFjayA9IGdldFN0YWNrID8gZ2V0U3RhY2soKSA6ICcnO1xuXG4gICAgICAgICAgcHJpbnRXYXJuaW5nKFxuICAgICAgICAgICAgJ0ZhaWxlZCAnICsgbG9jYXRpb24gKyAnIHR5cGU6ICcgKyBlcnJvci5tZXNzYWdlICsgKHN0YWNrICE9IG51bGwgPyBzdGFjayA6ICcnKVxuICAgICAgICAgICk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICB9XG4gIH1cbn1cblxuLyoqXG4gKiBSZXNldHMgd2FybmluZyBjYWNoZSB3aGVuIHRlc3RpbmcuXG4gKlxuICogQHByaXZhdGVcbiAqL1xuY2hlY2tQcm9wVHlwZXMucmVzZXRXYXJuaW5nQ2FjaGUgPSBmdW5jdGlvbigpIHtcbiAgaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicpIHtcbiAgICBsb2dnZWRUeXBlRmFpbHVyZXMgPSB7fTtcbiAgfVxufVxuXG5tb2R1bGUuZXhwb3J0cyA9IGNoZWNrUHJvcFR5cGVzO1xuIiwiLyoqXG4gKiBDb3B5cmlnaHQgKGMpIDIwMTMtcHJlc2VudCwgRmFjZWJvb2ssIEluYy5cbiAqXG4gKiBUaGlzIHNvdXJjZSBjb2RlIGlzIGxpY2Vuc2VkIHVuZGVyIHRoZSBNSVQgbGljZW5zZSBmb3VuZCBpbiB0aGVcbiAqIExJQ0VOU0UgZmlsZSBpbiB0aGUgcm9vdCBkaXJlY3Rvcnkgb2YgdGhpcyBzb3VyY2UgdHJlZS5cbiAqL1xuXG4ndXNlIHN0cmljdCc7XG5cbnZhciBSZWFjdElzID0gcmVxdWlyZSgncmVhY3QtaXMnKTtcbnZhciBhc3NpZ24gPSByZXF1aXJlKCdvYmplY3QtYXNzaWduJyk7XG5cbnZhciBSZWFjdFByb3BUeXBlc1NlY3JldCA9IHJlcXVpcmUoJy4vbGliL1JlYWN0UHJvcFR5cGVzU2VjcmV0Jyk7XG52YXIgaGFzID0gcmVxdWlyZSgnLi9saWIvaGFzJyk7XG52YXIgY2hlY2tQcm9wVHlwZXMgPSByZXF1aXJlKCcuL2NoZWNrUHJvcFR5cGVzJyk7XG5cbnZhciBwcmludFdhcm5pbmcgPSBmdW5jdGlvbigpIHt9O1xuXG5pZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09ICdwcm9kdWN0aW9uJykge1xuICBwcmludFdhcm5pbmcgPSBmdW5jdGlvbih0ZXh0KSB7XG4gICAgdmFyIG1lc3NhZ2UgPSAnV2FybmluZzogJyArIHRleHQ7XG4gICAgaWYgKHR5cGVvZiBjb25zb2xlICE9PSAndW5kZWZpbmVkJykge1xuICAgICAgY29uc29sZS5lcnJvcihtZXNzYWdlKTtcbiAgICB9XG4gICAgdHJ5IHtcbiAgICAgIC8vIC0tLSBXZWxjb21lIHRvIGRlYnVnZ2luZyBSZWFjdCAtLS1cbiAgICAgIC8vIFRoaXMgZXJyb3Igd2FzIHRocm93biBhcyBhIGNvbnZlbmllbmNlIHNvIHRoYXQgeW91IGNhbiB1c2UgdGhpcyBzdGFja1xuICAgICAgLy8gdG8gZmluZCB0aGUgY2FsbHNpdGUgdGhhdCBjYXVzZWQgdGhpcyB3YXJuaW5nIHRvIGZpcmUuXG4gICAgICB0aHJvdyBuZXcgRXJyb3IobWVzc2FnZSk7XG4gICAgfSBjYXRjaCAoeCkge31cbiAgfTtcbn1cblxuZnVuY3Rpb24gZW1wdHlGdW5jdGlvblRoYXRSZXR1cm5zTnVsbCgpIHtcbiAgcmV0dXJuIG51bGw7XG59XG5cbm1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24oaXNWYWxpZEVsZW1lbnQsIHRocm93T25EaXJlY3RBY2Nlc3MpIHtcbiAgLyogZ2xvYmFsIFN5bWJvbCAqL1xuICB2YXIgSVRFUkFUT1JfU1lNQk9MID0gdHlwZW9mIFN5bWJvbCA9PT0gJ2Z1bmN0aW9uJyAmJiBTeW1ib2wuaXRlcmF0b3I7XG4gIHZhciBGQVVYX0lURVJBVE9SX1NZTUJPTCA9ICdAQGl0ZXJhdG9yJzsgLy8gQmVmb3JlIFN5bWJvbCBzcGVjLlxuXG4gIC8qKlxuICAgKiBSZXR1cm5zIHRoZSBpdGVyYXRvciBtZXRob2QgZnVuY3Rpb24gY29udGFpbmVkIG9uIHRoZSBpdGVyYWJsZSBvYmplY3QuXG4gICAqXG4gICAqIEJlIHN1cmUgdG8gaW52b2tlIHRoZSBmdW5jdGlvbiB3aXRoIHRoZSBpdGVyYWJsZSBhcyBjb250ZXh0OlxuICAgKlxuICAgKiAgICAgdmFyIGl0ZXJhdG9yRm4gPSBnZXRJdGVyYXRvckZuKG15SXRlcmFibGUpO1xuICAgKiAgICAgaWYgKGl0ZXJhdG9yRm4pIHtcbiAgICogICAgICAgdmFyIGl0ZXJhdG9yID0gaXRlcmF0b3JGbi5jYWxsKG15SXRlcmFibGUpO1xuICAgKiAgICAgICAuLi5cbiAgICogICAgIH1cbiAgICpcbiAgICogQHBhcmFtIHs/b2JqZWN0fSBtYXliZUl0ZXJhYmxlXG4gICAqIEByZXR1cm4gez9mdW5jdGlvbn1cbiAgICovXG4gIGZ1bmN0aW9uIGdldEl0ZXJhdG9yRm4obWF5YmVJdGVyYWJsZSkge1xuICAgIHZhciBpdGVyYXRvckZuID0gbWF5YmVJdGVyYWJsZSAmJiAoSVRFUkFUT1JfU1lNQk9MICYmIG1heWJlSXRlcmFibGVbSVRFUkFUT1JfU1lNQk9MXSB8fCBtYXliZUl0ZXJhYmxlW0ZBVVhfSVRFUkFUT1JfU1lNQk9MXSk7XG4gICAgaWYgKHR5cGVvZiBpdGVyYXRvckZuID09PSAnZnVuY3Rpb24nKSB7XG4gICAgICByZXR1cm4gaXRlcmF0b3JGbjtcbiAgICB9XG4gIH1cblxuICAvKipcbiAgICogQ29sbGVjdGlvbiBvZiBtZXRob2RzIHRoYXQgYWxsb3cgZGVjbGFyYXRpb24gYW5kIHZhbGlkYXRpb24gb2YgcHJvcHMgdGhhdCBhcmVcbiAgICogc3VwcGxpZWQgdG8gUmVhY3QgY29tcG9uZW50cy4gRXhhbXBsZSB1c2FnZTpcbiAgICpcbiAgICogICB2YXIgUHJvcHMgPSByZXF1aXJlKCdSZWFjdFByb3BUeXBlcycpO1xuICAgKiAgIHZhciBNeUFydGljbGUgPSBSZWFjdC5jcmVhdGVDbGFzcyh7XG4gICAqICAgICBwcm9wVHlwZXM6IHtcbiAgICogICAgICAgLy8gQW4gb3B0aW9uYWwgc3RyaW5nIHByb3AgbmFtZWQgXCJkZXNjcmlwdGlvblwiLlxuICAgKiAgICAgICBkZXNjcmlwdGlvbjogUHJvcHMuc3RyaW5nLFxuICAgKlxuICAgKiAgICAgICAvLyBBIHJlcXVpcmVkIGVudW0gcHJvcCBuYW1lZCBcImNhdGVnb3J5XCIuXG4gICAqICAgICAgIGNhdGVnb3J5OiBQcm9wcy5vbmVPZihbJ05ld3MnLCdQaG90b3MnXSkuaXNSZXF1aXJlZCxcbiAgICpcbiAgICogICAgICAgLy8gQSBwcm9wIG5hbWVkIFwiZGlhbG9nXCIgdGhhdCByZXF1aXJlcyBhbiBpbnN0YW5jZSBvZiBEaWFsb2cuXG4gICAqICAgICAgIGRpYWxvZzogUHJvcHMuaW5zdGFuY2VPZihEaWFsb2cpLmlzUmVxdWlyZWRcbiAgICogICAgIH0sXG4gICAqICAgICByZW5kZXI6IGZ1bmN0aW9uKCkgeyAuLi4gfVxuICAgKiAgIH0pO1xuICAgKlxuICAgKiBBIG1vcmUgZm9ybWFsIHNwZWNpZmljYXRpb24gb2YgaG93IHRoZXNlIG1ldGhvZHMgYXJlIHVzZWQ6XG4gICAqXG4gICAqICAgdHlwZSA6PSBhcnJheXxib29sfGZ1bmN8b2JqZWN0fG51bWJlcnxzdHJpbmd8b25lT2YoWy4uLl0pfGluc3RhbmNlT2YoLi4uKVxuICAgKiAgIGRlY2wgOj0gUmVhY3RQcm9wVHlwZXMue3R5cGV9KC5pc1JlcXVpcmVkKT9cbiAgICpcbiAgICogRWFjaCBhbmQgZXZlcnkgZGVjbGFyYXRpb24gcHJvZHVjZXMgYSBmdW5jdGlvbiB3aXRoIHRoZSBzYW1lIHNpZ25hdHVyZS4gVGhpc1xuICAgKiBhbGxvd3MgdGhlIGNyZWF0aW9uIG9mIGN1c3RvbSB2YWxpZGF0aW9uIGZ1bmN0aW9ucy4gRm9yIGV4YW1wbGU6XG4gICAqXG4gICAqICB2YXIgTXlMaW5rID0gUmVhY3QuY3JlYXRlQ2xhc3Moe1xuICAgKiAgICBwcm9wVHlwZXM6IHtcbiAgICogICAgICAvLyBBbiBvcHRpb25hbCBzdHJpbmcgb3IgVVJJIHByb3AgbmFtZWQgXCJocmVmXCIuXG4gICAqICAgICAgaHJlZjogZnVuY3Rpb24ocHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lKSB7XG4gICAqICAgICAgICB2YXIgcHJvcFZhbHVlID0gcHJvcHNbcHJvcE5hbWVdO1xuICAgKiAgICAgICAgaWYgKHByb3BWYWx1ZSAhPSBudWxsICYmIHR5cGVvZiBwcm9wVmFsdWUgIT09ICdzdHJpbmcnICYmXG4gICAqICAgICAgICAgICAgIShwcm9wVmFsdWUgaW5zdGFuY2VvZiBVUkkpKSB7XG4gICAqICAgICAgICAgIHJldHVybiBuZXcgRXJyb3IoXG4gICAqICAgICAgICAgICAgJ0V4cGVjdGVkIGEgc3RyaW5nIG9yIGFuIFVSSSBmb3IgJyArIHByb3BOYW1lICsgJyBpbiAnICtcbiAgICogICAgICAgICAgICBjb21wb25lbnROYW1lXG4gICAqICAgICAgICAgICk7XG4gICAqICAgICAgICB9XG4gICAqICAgICAgfVxuICAgKiAgICB9LFxuICAgKiAgICByZW5kZXI6IGZ1bmN0aW9uKCkgey4uLn1cbiAgICogIH0pO1xuICAgKlxuICAgKiBAaW50ZXJuYWxcbiAgICovXG5cbiAgdmFyIEFOT05ZTU9VUyA9ICc8PGFub255bW91cz4+JztcblxuICAvLyBJbXBvcnRhbnQhXG4gIC8vIEtlZXAgdGhpcyBsaXN0IGluIHN5bmMgd2l0aCBwcm9kdWN0aW9uIHZlcnNpb24gaW4gYC4vZmFjdG9yeVdpdGhUaHJvd2luZ1NoaW1zLmpzYC5cbiAgdmFyIFJlYWN0UHJvcFR5cGVzID0ge1xuICAgIGFycmF5OiBjcmVhdGVQcmltaXRpdmVUeXBlQ2hlY2tlcignYXJyYXknKSxcbiAgICBiaWdpbnQ6IGNyZWF0ZVByaW1pdGl2ZVR5cGVDaGVja2VyKCdiaWdpbnQnKSxcbiAgICBib29sOiBjcmVhdGVQcmltaXRpdmVUeXBlQ2hlY2tlcignYm9vbGVhbicpLFxuICAgIGZ1bmM6IGNyZWF0ZVByaW1pdGl2ZVR5cGVDaGVja2VyKCdmdW5jdGlvbicpLFxuICAgIG51bWJlcjogY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIoJ251bWJlcicpLFxuICAgIG9iamVjdDogY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIoJ29iamVjdCcpLFxuICAgIHN0cmluZzogY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIoJ3N0cmluZycpLFxuICAgIHN5bWJvbDogY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIoJ3N5bWJvbCcpLFxuXG4gICAgYW55OiBjcmVhdGVBbnlUeXBlQ2hlY2tlcigpLFxuICAgIGFycmF5T2Y6IGNyZWF0ZUFycmF5T2ZUeXBlQ2hlY2tlcixcbiAgICBlbGVtZW50OiBjcmVhdGVFbGVtZW50VHlwZUNoZWNrZXIoKSxcbiAgICBlbGVtZW50VHlwZTogY3JlYXRlRWxlbWVudFR5cGVUeXBlQ2hlY2tlcigpLFxuICAgIGluc3RhbmNlT2Y6IGNyZWF0ZUluc3RhbmNlVHlwZUNoZWNrZXIsXG4gICAgbm9kZTogY3JlYXRlTm9kZUNoZWNrZXIoKSxcbiAgICBvYmplY3RPZjogY3JlYXRlT2JqZWN0T2ZUeXBlQ2hlY2tlcixcbiAgICBvbmVPZjogY3JlYXRlRW51bVR5cGVDaGVja2VyLFxuICAgIG9uZU9mVHlwZTogY3JlYXRlVW5pb25UeXBlQ2hlY2tlcixcbiAgICBzaGFwZTogY3JlYXRlU2hhcGVUeXBlQ2hlY2tlcixcbiAgICBleGFjdDogY3JlYXRlU3RyaWN0U2hhcGVUeXBlQ2hlY2tlcixcbiAgfTtcblxuICAvKipcbiAgICogaW5saW5lZCBPYmplY3QuaXMgcG9seWZpbGwgdG8gYXZvaWQgcmVxdWlyaW5nIGNvbnN1bWVycyBzaGlwIHRoZWlyIG93blxuICAgKiBodHRwczovL2RldmVsb3Blci5tb3ppbGxhLm9yZy9lbi1VUy9kb2NzL1dlYi9KYXZhU2NyaXB0L1JlZmVyZW5jZS9HbG9iYWxfT2JqZWN0cy9PYmplY3QvaXNcbiAgICovXG4gIC8qZXNsaW50LWRpc2FibGUgbm8tc2VsZi1jb21wYXJlKi9cbiAgZnVuY3Rpb24gaXMoeCwgeSkge1xuICAgIC8vIFNhbWVWYWx1ZSBhbGdvcml0aG1cbiAgICBpZiAoeCA9PT0geSkge1xuICAgICAgLy8gU3RlcHMgMS01LCA3LTEwXG4gICAgICAvLyBTdGVwcyA2LmItNi5lOiArMCAhPSAtMFxuICAgICAgcmV0dXJuIHggIT09IDAgfHwgMSAvIHggPT09IDEgLyB5O1xuICAgIH0gZWxzZSB7XG4gICAgICAvLyBTdGVwIDYuYTogTmFOID09IE5hTlxuICAgICAgcmV0dXJuIHggIT09IHggJiYgeSAhPT0geTtcbiAgICB9XG4gIH1cbiAgLyplc2xpbnQtZW5hYmxlIG5vLXNlbGYtY29tcGFyZSovXG5cbiAgLyoqXG4gICAqIFdlIHVzZSBhbiBFcnJvci1saWtlIG9iamVjdCBmb3IgYmFja3dhcmQgY29tcGF0aWJpbGl0eSBhcyBwZW9wbGUgbWF5IGNhbGxcbiAgICogUHJvcFR5cGVzIGRpcmVjdGx5IGFuZCBpbnNwZWN0IHRoZWlyIG91dHB1dC4gSG93ZXZlciwgd2UgZG9uJ3QgdXNlIHJlYWxcbiAgICogRXJyb3JzIGFueW1vcmUuIFdlIGRvbid0IGluc3BlY3QgdGhlaXIgc3RhY2sgYW55d2F5LCBhbmQgY3JlYXRpbmcgdGhlbVxuICAgKiBpcyBwcm9oaWJpdGl2ZWx5IGV4cGVuc2l2ZSBpZiB0aGV5IGFyZSBjcmVhdGVkIHRvbyBvZnRlbiwgc3VjaCBhcyB3aGF0XG4gICAqIGhhcHBlbnMgaW4gb25lT2ZUeXBlKCkgZm9yIGFueSB0eXBlIGJlZm9yZSB0aGUgb25lIHRoYXQgbWF0Y2hlZC5cbiAgICovXG4gIGZ1bmN0aW9uIFByb3BUeXBlRXJyb3IobWVzc2FnZSwgZGF0YSkge1xuICAgIHRoaXMubWVzc2FnZSA9IG1lc3NhZ2U7XG4gICAgdGhpcy5kYXRhID0gZGF0YSAmJiB0eXBlb2YgZGF0YSA9PT0gJ29iamVjdCcgPyBkYXRhOiB7fTtcbiAgICB0aGlzLnN0YWNrID0gJyc7XG4gIH1cbiAgLy8gTWFrZSBgaW5zdGFuY2VvZiBFcnJvcmAgc3RpbGwgd29yayBmb3IgcmV0dXJuZWQgZXJyb3JzLlxuICBQcm9wVHlwZUVycm9yLnByb3RvdHlwZSA9IEVycm9yLnByb3RvdHlwZTtcblxuICBmdW5jdGlvbiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSkge1xuICAgIGlmIChwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gJ3Byb2R1Y3Rpb24nKSB7XG4gICAgICB2YXIgbWFudWFsUHJvcFR5cGVDYWxsQ2FjaGUgPSB7fTtcbiAgICAgIHZhciBtYW51YWxQcm9wVHlwZVdhcm5pbmdDb3VudCA9IDA7XG4gICAgfVxuICAgIGZ1bmN0aW9uIGNoZWNrVHlwZShpc1JlcXVpcmVkLCBwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUsIHNlY3JldCkge1xuICAgICAgY29tcG9uZW50TmFtZSA9IGNvbXBvbmVudE5hbWUgfHwgQU5PTllNT1VTO1xuICAgICAgcHJvcEZ1bGxOYW1lID0gcHJvcEZ1bGxOYW1lIHx8IHByb3BOYW1lO1xuXG4gICAgICBpZiAoc2VjcmV0ICE9PSBSZWFjdFByb3BUeXBlc1NlY3JldCkge1xuICAgICAgICBpZiAodGhyb3dPbkRpcmVjdEFjY2Vzcykge1xuICAgICAgICAgIC8vIE5ldyBiZWhhdmlvciBvbmx5IGZvciB1c2VycyBvZiBgcHJvcC10eXBlc2AgcGFja2FnZVxuICAgICAgICAgIHZhciBlcnIgPSBuZXcgRXJyb3IoXG4gICAgICAgICAgICAnQ2FsbGluZyBQcm9wVHlwZXMgdmFsaWRhdG9ycyBkaXJlY3RseSBpcyBub3Qgc3VwcG9ydGVkIGJ5IHRoZSBgcHJvcC10eXBlc2AgcGFja2FnZS4gJyArXG4gICAgICAgICAgICAnVXNlIGBQcm9wVHlwZXMuY2hlY2tQcm9wVHlwZXMoKWAgdG8gY2FsbCB0aGVtLiAnICtcbiAgICAgICAgICAgICdSZWFkIG1vcmUgYXQgaHR0cDovL2ZiLm1lL3VzZS1jaGVjay1wcm9wLXR5cGVzJ1xuICAgICAgICAgICk7XG4gICAgICAgICAgZXJyLm5hbWUgPSAnSW52YXJpYW50IFZpb2xhdGlvbic7XG4gICAgICAgICAgdGhyb3cgZXJyO1xuICAgICAgICB9IGVsc2UgaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicgJiYgdHlwZW9mIGNvbnNvbGUgIT09ICd1bmRlZmluZWQnKSB7XG4gICAgICAgICAgLy8gT2xkIGJlaGF2aW9yIGZvciBwZW9wbGUgdXNpbmcgUmVhY3QuUHJvcFR5cGVzXG4gICAgICAgICAgdmFyIGNhY2hlS2V5ID0gY29tcG9uZW50TmFtZSArICc6JyArIHByb3BOYW1lO1xuICAgICAgICAgIGlmIChcbiAgICAgICAgICAgICFtYW51YWxQcm9wVHlwZUNhbGxDYWNoZVtjYWNoZUtleV0gJiZcbiAgICAgICAgICAgIC8vIEF2b2lkIHNwYW1taW5nIHRoZSBjb25zb2xlIGJlY2F1c2UgdGhleSBhcmUgb2Z0ZW4gbm90IGFjdGlvbmFibGUgZXhjZXB0IGZvciBsaWIgYXV0aG9yc1xuICAgICAgICAgICAgbWFudWFsUHJvcFR5cGVXYXJuaW5nQ291bnQgPCAzXG4gICAgICAgICAgKSB7XG4gICAgICAgICAgICBwcmludFdhcm5pbmcoXG4gICAgICAgICAgICAgICdZb3UgYXJlIG1hbnVhbGx5IGNhbGxpbmcgYSBSZWFjdC5Qcm9wVHlwZXMgdmFsaWRhdGlvbiAnICtcbiAgICAgICAgICAgICAgJ2Z1bmN0aW9uIGZvciB0aGUgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBwcm9wIG9uIGAnICsgY29tcG9uZW50TmFtZSArICdgLiBUaGlzIGlzIGRlcHJlY2F0ZWQgJyArXG4gICAgICAgICAgICAgICdhbmQgd2lsbCB0aHJvdyBpbiB0aGUgc3RhbmRhbG9uZSBgcHJvcC10eXBlc2AgcGFja2FnZS4gJyArXG4gICAgICAgICAgICAgICdZb3UgbWF5IGJlIHNlZWluZyB0aGlzIHdhcm5pbmcgZHVlIHRvIGEgdGhpcmQtcGFydHkgUHJvcFR5cGVzICcgK1xuICAgICAgICAgICAgICAnbGlicmFyeS4gU2VlIGh0dHBzOi8vZmIubWUvcmVhY3Qtd2FybmluZy1kb250LWNhbGwtcHJvcHR5cGVzICcgKyAnZm9yIGRldGFpbHMuJ1xuICAgICAgICAgICAgKTtcbiAgICAgICAgICAgIG1hbnVhbFByb3BUeXBlQ2FsbENhY2hlW2NhY2hlS2V5XSA9IHRydWU7XG4gICAgICAgICAgICBtYW51YWxQcm9wVHlwZVdhcm5pbmdDb3VudCsrO1xuICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgaWYgKHByb3BzW3Byb3BOYW1lXSA9PSBudWxsKSB7XG4gICAgICAgIGlmIChpc1JlcXVpcmVkKSB7XG4gICAgICAgICAgaWYgKHByb3BzW3Byb3BOYW1lXSA9PT0gbnVsbCkge1xuICAgICAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdUaGUgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIGlzIG1hcmtlZCBhcyByZXF1aXJlZCAnICsgKCdpbiBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgYnV0IGl0cyB2YWx1ZSBpcyBgbnVsbGAuJykpO1xuICAgICAgICAgIH1cbiAgICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ1RoZSAnICsgbG9jYXRpb24gKyAnIGAnICsgcHJvcEZ1bGxOYW1lICsgJ2AgaXMgbWFya2VkIGFzIHJlcXVpcmVkIGluICcgKyAoJ2AnICsgY29tcG9uZW50TmFtZSArICdgLCBidXQgaXRzIHZhbHVlIGlzIGB1bmRlZmluZWRgLicpKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHJldHVybiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpO1xuICAgICAgfVxuICAgIH1cblxuICAgIHZhciBjaGFpbmVkQ2hlY2tUeXBlID0gY2hlY2tUeXBlLmJpbmQobnVsbCwgZmFsc2UpO1xuICAgIGNoYWluZWRDaGVja1R5cGUuaXNSZXF1aXJlZCA9IGNoZWNrVHlwZS5iaW5kKG51bGwsIHRydWUpO1xuXG4gICAgcmV0dXJuIGNoYWluZWRDaGVja1R5cGU7XG4gIH1cblxuICBmdW5jdGlvbiBjcmVhdGVQcmltaXRpdmVUeXBlQ2hlY2tlcihleHBlY3RlZFR5cGUpIHtcbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUsIHNlY3JldCkge1xuICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICAgIHZhciBwcm9wVHlwZSA9IGdldFByb3BUeXBlKHByb3BWYWx1ZSk7XG4gICAgICBpZiAocHJvcFR5cGUgIT09IGV4cGVjdGVkVHlwZSkge1xuICAgICAgICAvLyBgcHJvcFZhbHVlYCBiZWluZyBpbnN0YW5jZSBvZiwgc2F5LCBkYXRlL3JlZ2V4cCwgcGFzcyB0aGUgJ29iamVjdCdcbiAgICAgICAgLy8gY2hlY2ssIGJ1dCB3ZSBjYW4gb2ZmZXIgYSBtb3JlIHByZWNpc2UgZXJyb3IgbWVzc2FnZSBoZXJlIHJhdGhlciB0aGFuXG4gICAgICAgIC8vICdvZiB0eXBlIGBvYmplY3RgJy5cbiAgICAgICAgdmFyIHByZWNpc2VUeXBlID0gZ2V0UHJlY2lzZVR5cGUocHJvcFZhbHVlKTtcblxuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoXG4gICAgICAgICAgJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIHR5cGUgJyArICgnYCcgKyBwcmVjaXNlVHlwZSArICdgIHN1cHBsaWVkIHRvIGAnICsgY29tcG9uZW50TmFtZSArICdgLCBleHBlY3RlZCAnKSArICgnYCcgKyBleHBlY3RlZFR5cGUgKyAnYC4nKSxcbiAgICAgICAgICB7ZXhwZWN0ZWRUeXBlOiBleHBlY3RlZFR5cGV9XG4gICAgICAgICk7XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZUFueVR5cGVDaGVja2VyKCkge1xuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcihlbXB0eUZ1bmN0aW9uVGhhdFJldHVybnNOdWxsKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZUFycmF5T2ZUeXBlQ2hlY2tlcih0eXBlQ2hlY2tlcikge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgaWYgKHR5cGVvZiB0eXBlQ2hlY2tlciAhPT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ1Byb3BlcnR5IGAnICsgcHJvcEZ1bGxOYW1lICsgJ2Agb2YgY29tcG9uZW50IGAnICsgY29tcG9uZW50TmFtZSArICdgIGhhcyBpbnZhbGlkIFByb3BUeXBlIG5vdGF0aW9uIGluc2lkZSBhcnJheU9mLicpO1xuICAgICAgfVxuICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICAgIGlmICghQXJyYXkuaXNBcnJheShwcm9wVmFsdWUpKSB7XG4gICAgICAgIHZhciBwcm9wVHlwZSA9IGdldFByb3BUeXBlKHByb3BWYWx1ZSk7XG4gICAgICAgIHJldHVybiBuZXcgUHJvcFR5cGVFcnJvcignSW52YWxpZCAnICsgbG9jYXRpb24gKyAnIGAnICsgcHJvcEZ1bGxOYW1lICsgJ2Agb2YgdHlwZSAnICsgKCdgJyArIHByb3BUeXBlICsgJ2Agc3VwcGxpZWQgdG8gYCcgKyBjb21wb25lbnROYW1lICsgJ2AsIGV4cGVjdGVkIGFuIGFycmF5LicpKTtcbiAgICAgIH1cbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgcHJvcFZhbHVlLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIHZhciBlcnJvciA9IHR5cGVDaGVja2VyKHByb3BWYWx1ZSwgaSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSArICdbJyArIGkgKyAnXScsIFJlYWN0UHJvcFR5cGVzU2VjcmV0KTtcbiAgICAgICAgaWYgKGVycm9yIGluc3RhbmNlb2YgRXJyb3IpIHtcbiAgICAgICAgICByZXR1cm4gZXJyb3I7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbiAgICByZXR1cm4gY3JlYXRlQ2hhaW5hYmxlVHlwZUNoZWNrZXIodmFsaWRhdGUpO1xuICB9XG5cbiAgZnVuY3Rpb24gY3JlYXRlRWxlbWVudFR5cGVDaGVja2VyKCkge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICAgIGlmICghaXNWYWxpZEVsZW1lbnQocHJvcFZhbHVlKSkge1xuICAgICAgICB2YXIgcHJvcFR5cGUgPSBnZXRQcm9wVHlwZShwcm9wVmFsdWUpO1xuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIHR5cGUgJyArICgnYCcgKyBwcm9wVHlwZSArICdgIHN1cHBsaWVkIHRvIGAnICsgY29tcG9uZW50TmFtZSArICdgLCBleHBlY3RlZCBhIHNpbmdsZSBSZWFjdEVsZW1lbnQuJykpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSk7XG4gIH1cblxuICBmdW5jdGlvbiBjcmVhdGVFbGVtZW50VHlwZVR5cGVDaGVja2VyKCkge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICAgIGlmICghUmVhY3RJcy5pc1ZhbGlkRWxlbWVudFR5cGUocHJvcFZhbHVlKSkge1xuICAgICAgICB2YXIgcHJvcFR5cGUgPSBnZXRQcm9wVHlwZShwcm9wVmFsdWUpO1xuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIHR5cGUgJyArICgnYCcgKyBwcm9wVHlwZSArICdgIHN1cHBsaWVkIHRvIGAnICsgY29tcG9uZW50TmFtZSArICdgLCBleHBlY3RlZCBhIHNpbmdsZSBSZWFjdEVsZW1lbnQgdHlwZS4nKSk7XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZUluc3RhbmNlVHlwZUNoZWNrZXIoZXhwZWN0ZWRDbGFzcykge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgaWYgKCEocHJvcHNbcHJvcE5hbWVdIGluc3RhbmNlb2YgZXhwZWN0ZWRDbGFzcykpIHtcbiAgICAgICAgdmFyIGV4cGVjdGVkQ2xhc3NOYW1lID0gZXhwZWN0ZWRDbGFzcy5uYW1lIHx8IEFOT05ZTU9VUztcbiAgICAgICAgdmFyIGFjdHVhbENsYXNzTmFtZSA9IGdldENsYXNzTmFtZShwcm9wc1twcm9wTmFtZV0pO1xuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIHR5cGUgJyArICgnYCcgKyBhY3R1YWxDbGFzc05hbWUgKyAnYCBzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgJykgKyAoJ2luc3RhbmNlIG9mIGAnICsgZXhwZWN0ZWRDbGFzc05hbWUgKyAnYC4nKSk7XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZUVudW1UeXBlQ2hlY2tlcihleHBlY3RlZFZhbHVlcykge1xuICAgIGlmICghQXJyYXkuaXNBcnJheShleHBlY3RlZFZhbHVlcykpIHtcbiAgICAgIGlmIChwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gJ3Byb2R1Y3Rpb24nKSB7XG4gICAgICAgIGlmIChhcmd1bWVudHMubGVuZ3RoID4gMSkge1xuICAgICAgICAgIHByaW50V2FybmluZyhcbiAgICAgICAgICAgICdJbnZhbGlkIGFyZ3VtZW50cyBzdXBwbGllZCB0byBvbmVPZiwgZXhwZWN0ZWQgYW4gYXJyYXksIGdvdCAnICsgYXJndW1lbnRzLmxlbmd0aCArICcgYXJndW1lbnRzLiAnICtcbiAgICAgICAgICAgICdBIGNvbW1vbiBtaXN0YWtlIGlzIHRvIHdyaXRlIG9uZU9mKHgsIHksIHopIGluc3RlYWQgb2Ygb25lT2YoW3gsIHksIHpdKS4nXG4gICAgICAgICAgKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBwcmludFdhcm5pbmcoJ0ludmFsaWQgYXJndW1lbnQgc3VwcGxpZWQgdG8gb25lT2YsIGV4cGVjdGVkIGFuIGFycmF5LicpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICByZXR1cm4gZW1wdHlGdW5jdGlvblRoYXRSZXR1cm5zTnVsbDtcbiAgICB9XG5cbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpIHtcbiAgICAgIHZhciBwcm9wVmFsdWUgPSBwcm9wc1twcm9wTmFtZV07XG4gICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGV4cGVjdGVkVmFsdWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIGlmIChpcyhwcm9wVmFsdWUsIGV4cGVjdGVkVmFsdWVzW2ldKSkge1xuICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICB9XG4gICAgICB9XG5cbiAgICAgIHZhciB2YWx1ZXNTdHJpbmcgPSBKU09OLnN0cmluZ2lmeShleHBlY3RlZFZhbHVlcywgZnVuY3Rpb24gcmVwbGFjZXIoa2V5LCB2YWx1ZSkge1xuICAgICAgICB2YXIgdHlwZSA9IGdldFByZWNpc2VUeXBlKHZhbHVlKTtcbiAgICAgICAgaWYgKHR5cGUgPT09ICdzeW1ib2wnKSB7XG4gICAgICAgICAgcmV0dXJuIFN0cmluZyh2YWx1ZSk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHZhbHVlO1xuICAgICAgfSk7XG4gICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIHZhbHVlIGAnICsgU3RyaW5nKHByb3BWYWx1ZSkgKyAnYCAnICsgKCdzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgb25lIG9mICcgKyB2YWx1ZXNTdHJpbmcgKyAnLicpKTtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZU9iamVjdE9mVHlwZUNoZWNrZXIodHlwZUNoZWNrZXIpIHtcbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpIHtcbiAgICAgIGlmICh0eXBlb2YgdHlwZUNoZWNrZXIgIT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdQcm9wZXJ0eSBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIGNvbXBvbmVudCBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCBoYXMgaW52YWxpZCBQcm9wVHlwZSBub3RhdGlvbiBpbnNpZGUgb2JqZWN0T2YuJyk7XG4gICAgICB9XG4gICAgICB2YXIgcHJvcFZhbHVlID0gcHJvcHNbcHJvcE5hbWVdO1xuICAgICAgdmFyIHByb3BUeXBlID0gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKTtcbiAgICAgIGlmIChwcm9wVHlwZSAhPT0gJ29iamVjdCcpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiB0eXBlICcgKyAoJ2AnICsgcHJvcFR5cGUgKyAnYCBzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgYW4gb2JqZWN0LicpKTtcbiAgICAgIH1cbiAgICAgIGZvciAodmFyIGtleSBpbiBwcm9wVmFsdWUpIHtcbiAgICAgICAgaWYgKGhhcyhwcm9wVmFsdWUsIGtleSkpIHtcbiAgICAgICAgICB2YXIgZXJyb3IgPSB0eXBlQ2hlY2tlcihwcm9wVmFsdWUsIGtleSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSArICcuJyArIGtleSwgUmVhY3RQcm9wVHlwZXNTZWNyZXQpO1xuICAgICAgICAgIGlmIChlcnJvciBpbnN0YW5jZW9mIEVycm9yKSB7XG4gICAgICAgICAgICByZXR1cm4gZXJyb3I7XG4gICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZVVuaW9uVHlwZUNoZWNrZXIoYXJyYXlPZlR5cGVDaGVja2Vycykge1xuICAgIGlmICghQXJyYXkuaXNBcnJheShhcnJheU9mVHlwZUNoZWNrZXJzKSkge1xuICAgICAgcHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09ICdwcm9kdWN0aW9uJyA/IHByaW50V2FybmluZygnSW52YWxpZCBhcmd1bWVudCBzdXBwbGllZCB0byBvbmVPZlR5cGUsIGV4cGVjdGVkIGFuIGluc3RhbmNlIG9mIGFycmF5LicpIDogdm9pZCAwO1xuICAgICAgcmV0dXJuIGVtcHR5RnVuY3Rpb25UaGF0UmV0dXJuc051bGw7XG4gICAgfVxuXG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBhcnJheU9mVHlwZUNoZWNrZXJzLmxlbmd0aDsgaSsrKSB7XG4gICAgICB2YXIgY2hlY2tlciA9IGFycmF5T2ZUeXBlQ2hlY2tlcnNbaV07XG4gICAgICBpZiAodHlwZW9mIGNoZWNrZXIgIT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgcHJpbnRXYXJuaW5nKFxuICAgICAgICAgICdJbnZhbGlkIGFyZ3VtZW50IHN1cHBsaWVkIHRvIG9uZU9mVHlwZS4gRXhwZWN0ZWQgYW4gYXJyYXkgb2YgY2hlY2sgZnVuY3Rpb25zLCBidXQgJyArXG4gICAgICAgICAgJ3JlY2VpdmVkICcgKyBnZXRQb3N0Zml4Rm9yVHlwZVdhcm5pbmcoY2hlY2tlcikgKyAnIGF0IGluZGV4ICcgKyBpICsgJy4nXG4gICAgICAgICk7XG4gICAgICAgIHJldHVybiBlbXB0eUZ1bmN0aW9uVGhhdFJldHVybnNOdWxsO1xuICAgICAgfVxuICAgIH1cblxuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgdmFyIGV4cGVjdGVkVHlwZXMgPSBbXTtcbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgYXJyYXlPZlR5cGVDaGVja2Vycy5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgY2hlY2tlciA9IGFycmF5T2ZUeXBlQ2hlY2tlcnNbaV07XG4gICAgICAgIHZhciBjaGVja2VyUmVzdWx0ID0gY2hlY2tlcihwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUsIFJlYWN0UHJvcFR5cGVzU2VjcmV0KTtcbiAgICAgICAgaWYgKGNoZWNrZXJSZXN1bHQgPT0gbnVsbCkge1xuICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICB9XG4gICAgICAgIGlmIChjaGVja2VyUmVzdWx0LmRhdGEgJiYgaGFzKGNoZWNrZXJSZXN1bHQuZGF0YSwgJ2V4cGVjdGVkVHlwZScpKSB7XG4gICAgICAgICAgZXhwZWN0ZWRUeXBlcy5wdXNoKGNoZWNrZXJSZXN1bHQuZGF0YS5leHBlY3RlZFR5cGUpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICB2YXIgZXhwZWN0ZWRUeXBlc01lc3NhZ2UgPSAoZXhwZWN0ZWRUeXBlcy5sZW5ndGggPiAwKSA/ICcsIGV4cGVjdGVkIG9uZSBvZiB0eXBlIFsnICsgZXhwZWN0ZWRUeXBlcy5qb2luKCcsICcpICsgJ10nOiAnJztcbiAgICAgIHJldHVybiBuZXcgUHJvcFR5cGVFcnJvcignSW52YWxpZCAnICsgbG9jYXRpb24gKyAnIGAnICsgcHJvcEZ1bGxOYW1lICsgJ2Agc3VwcGxpZWQgdG8gJyArICgnYCcgKyBjb21wb25lbnROYW1lICsgJ2AnICsgZXhwZWN0ZWRUeXBlc01lc3NhZ2UgKyAnLicpKTtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZU5vZGVDaGVja2VyKCkge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgaWYgKCFpc05vZGUocHJvcHNbcHJvcE5hbWVdKSkge1xuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIHN1cHBsaWVkIHRvICcgKyAoJ2AnICsgY29tcG9uZW50TmFtZSArICdgLCBleHBlY3RlZCBhIFJlYWN0Tm9kZS4nKSk7XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGludmFsaWRWYWxpZGF0b3JFcnJvcihjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lLCBrZXksIHR5cGUpIHtcbiAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoXG4gICAgICAoY29tcG9uZW50TmFtZSB8fCAnUmVhY3QgY2xhc3MnKSArICc6ICcgKyBsb2NhdGlvbiArICcgdHlwZSBgJyArIHByb3BGdWxsTmFtZSArICcuJyArIGtleSArICdgIGlzIGludmFsaWQ7ICcgK1xuICAgICAgJ2l0IG11c3QgYmUgYSBmdW5jdGlvbiwgdXN1YWxseSBmcm9tIHRoZSBgcHJvcC10eXBlc2AgcGFja2FnZSwgYnV0IHJlY2VpdmVkIGAnICsgdHlwZSArICdgLidcbiAgICApO1xuICB9XG5cbiAgZnVuY3Rpb24gY3JlYXRlU2hhcGVUeXBlQ2hlY2tlcihzaGFwZVR5cGVzKSB7XG4gICAgZnVuY3Rpb24gdmFsaWRhdGUocHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lKSB7XG4gICAgICB2YXIgcHJvcFZhbHVlID0gcHJvcHNbcHJvcE5hbWVdO1xuICAgICAgdmFyIHByb3BUeXBlID0gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKTtcbiAgICAgIGlmIChwcm9wVHlwZSAhPT0gJ29iamVjdCcpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiB0eXBlIGAnICsgcHJvcFR5cGUgKyAnYCAnICsgKCdzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgYG9iamVjdGAuJykpO1xuICAgICAgfVxuICAgICAgZm9yICh2YXIga2V5IGluIHNoYXBlVHlwZXMpIHtcbiAgICAgICAgdmFyIGNoZWNrZXIgPSBzaGFwZVR5cGVzW2tleV07XG4gICAgICAgIGlmICh0eXBlb2YgY2hlY2tlciAhPT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICAgIHJldHVybiBpbnZhbGlkVmFsaWRhdG9yRXJyb3IoY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSwga2V5LCBnZXRQcmVjaXNlVHlwZShjaGVja2VyKSk7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGVycm9yID0gY2hlY2tlcihwcm9wVmFsdWUsIGtleSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSArICcuJyArIGtleSwgUmVhY3RQcm9wVHlwZXNTZWNyZXQpO1xuICAgICAgICBpZiAoZXJyb3IpIHtcbiAgICAgICAgICByZXR1cm4gZXJyb3I7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbiAgICByZXR1cm4gY3JlYXRlQ2hhaW5hYmxlVHlwZUNoZWNrZXIodmFsaWRhdGUpO1xuICB9XG5cbiAgZnVuY3Rpb24gY3JlYXRlU3RyaWN0U2hhcGVUeXBlQ2hlY2tlcihzaGFwZVR5cGVzKSB7XG4gICAgZnVuY3Rpb24gdmFsaWRhdGUocHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lKSB7XG4gICAgICB2YXIgcHJvcFZhbHVlID0gcHJvcHNbcHJvcE5hbWVdO1xuICAgICAgdmFyIHByb3BUeXBlID0gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKTtcbiAgICAgIGlmIChwcm9wVHlwZSAhPT0gJ29iamVjdCcpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiB0eXBlIGAnICsgcHJvcFR5cGUgKyAnYCAnICsgKCdzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgYG9iamVjdGAuJykpO1xuICAgICAgfVxuICAgICAgLy8gV2UgbmVlZCB0byBjaGVjayBhbGwga2V5cyBpbiBjYXNlIHNvbWUgYXJlIHJlcXVpcmVkIGJ1dCBtaXNzaW5nIGZyb20gcHJvcHMuXG4gICAgICB2YXIgYWxsS2V5cyA9IGFzc2lnbih7fSwgcHJvcHNbcHJvcE5hbWVdLCBzaGFwZVR5cGVzKTtcbiAgICAgIGZvciAodmFyIGtleSBpbiBhbGxLZXlzKSB7XG4gICAgICAgIHZhciBjaGVja2VyID0gc2hhcGVUeXBlc1trZXldO1xuICAgICAgICBpZiAoaGFzKHNoYXBlVHlwZXMsIGtleSkgJiYgdHlwZW9mIGNoZWNrZXIgIT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgICByZXR1cm4gaW52YWxpZFZhbGlkYXRvckVycm9yKGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUsIGtleSwgZ2V0UHJlY2lzZVR5cGUoY2hlY2tlcikpO1xuICAgICAgICB9XG4gICAgICAgIGlmICghY2hlY2tlcikge1xuICAgICAgICAgIHJldHVybiBuZXcgUHJvcFR5cGVFcnJvcihcbiAgICAgICAgICAgICdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBrZXkgYCcgKyBrZXkgKyAnYCBzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYC4nICtcbiAgICAgICAgICAgICdcXG5CYWQgb2JqZWN0OiAnICsgSlNPTi5zdHJpbmdpZnkocHJvcHNbcHJvcE5hbWVdLCBudWxsLCAnICAnKSArXG4gICAgICAgICAgICAnXFxuVmFsaWQga2V5czogJyArIEpTT04uc3RyaW5naWZ5KE9iamVjdC5rZXlzKHNoYXBlVHlwZXMpLCBudWxsLCAnICAnKVxuICAgICAgICAgICk7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGVycm9yID0gY2hlY2tlcihwcm9wVmFsdWUsIGtleSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSArICcuJyArIGtleSwgUmVhY3RQcm9wVHlwZXNTZWNyZXQpO1xuICAgICAgICBpZiAoZXJyb3IpIHtcbiAgICAgICAgICByZXR1cm4gZXJyb3I7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIHJldHVybiBudWxsO1xuICAgIH1cblxuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSk7XG4gIH1cblxuICBmdW5jdGlvbiBpc05vZGUocHJvcFZhbHVlKSB7XG4gICAgc3dpdGNoICh0eXBlb2YgcHJvcFZhbHVlKSB7XG4gICAgICBjYXNlICdudW1iZXInOlxuICAgICAgY2FzZSAnc3RyaW5nJzpcbiAgICAgIGNhc2UgJ3VuZGVmaW5lZCc6XG4gICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgY2FzZSAnYm9vbGVhbic6XG4gICAgICAgIHJldHVybiAhcHJvcFZhbHVlO1xuICAgICAgY2FzZSAnb2JqZWN0JzpcbiAgICAgICAgaWYgKEFycmF5LmlzQXJyYXkocHJvcFZhbHVlKSkge1xuICAgICAgICAgIHJldHVybiBwcm9wVmFsdWUuZXZlcnkoaXNOb2RlKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAocHJvcFZhbHVlID09PSBudWxsIHx8IGlzVmFsaWRFbGVtZW50KHByb3BWYWx1ZSkpIHtcbiAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgfVxuXG4gICAgICAgIHZhciBpdGVyYXRvckZuID0gZ2V0SXRlcmF0b3JGbihwcm9wVmFsdWUpO1xuICAgICAgICBpZiAoaXRlcmF0b3JGbikge1xuICAgICAgICAgIHZhciBpdGVyYXRvciA9IGl0ZXJhdG9yRm4uY2FsbChwcm9wVmFsdWUpO1xuICAgICAgICAgIHZhciBzdGVwO1xuICAgICAgICAgIGlmIChpdGVyYXRvckZuICE9PSBwcm9wVmFsdWUuZW50cmllcykge1xuICAgICAgICAgICAgd2hpbGUgKCEoc3RlcCA9IGl0ZXJhdG9yLm5leHQoKSkuZG9uZSkge1xuICAgICAgICAgICAgICBpZiAoIWlzTm9kZShzdGVwLnZhbHVlKSkge1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAvLyBJdGVyYXRvciB3aWxsIHByb3ZpZGUgZW50cnkgW2ssdl0gdHVwbGVzIHJhdGhlciB0aGFuIHZhbHVlcy5cbiAgICAgICAgICAgIHdoaWxlICghKHN0ZXAgPSBpdGVyYXRvci5uZXh0KCkpLmRvbmUpIHtcbiAgICAgICAgICAgICAgdmFyIGVudHJ5ID0gc3RlcC52YWx1ZTtcbiAgICAgICAgICAgICAgaWYgKGVudHJ5KSB7XG4gICAgICAgICAgICAgICAgaWYgKCFpc05vZGUoZW50cnlbMV0pKSB7XG4gICAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgfVxuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgfVxuXG4gICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgZGVmYXVsdDpcbiAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgIH1cbiAgfVxuXG4gIGZ1bmN0aW9uIGlzU3ltYm9sKHByb3BUeXBlLCBwcm9wVmFsdWUpIHtcbiAgICAvLyBOYXRpdmUgU3ltYm9sLlxuICAgIGlmIChwcm9wVHlwZSA9PT0gJ3N5bWJvbCcpIHtcbiAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cblxuICAgIC8vIGZhbHN5IHZhbHVlIGNhbid0IGJlIGEgU3ltYm9sXG4gICAgaWYgKCFwcm9wVmFsdWUpIHtcbiAgICAgIHJldHVybiBmYWxzZTtcbiAgICB9XG5cbiAgICAvLyAxOS40LjMuNSBTeW1ib2wucHJvdG90eXBlW0BAdG9TdHJpbmdUYWddID09PSAnU3ltYm9sJ1xuICAgIGlmIChwcm9wVmFsdWVbJ0BAdG9TdHJpbmdUYWcnXSA9PT0gJ1N5bWJvbCcpIHtcbiAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cblxuICAgIC8vIEZhbGxiYWNrIGZvciBub24tc3BlYyBjb21wbGlhbnQgU3ltYm9scyB3aGljaCBhcmUgcG9seWZpbGxlZC5cbiAgICBpZiAodHlwZW9mIFN5bWJvbCA9PT0gJ2Z1bmN0aW9uJyAmJiBwcm9wVmFsdWUgaW5zdGFuY2VvZiBTeW1ib2wpIHtcbiAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cblxuICAgIHJldHVybiBmYWxzZTtcbiAgfVxuXG4gIC8vIEVxdWl2YWxlbnQgb2YgYHR5cGVvZmAgYnV0IHdpdGggc3BlY2lhbCBoYW5kbGluZyBmb3IgYXJyYXkgYW5kIHJlZ2V4cC5cbiAgZnVuY3Rpb24gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKSB7XG4gICAgdmFyIHByb3BUeXBlID0gdHlwZW9mIHByb3BWYWx1ZTtcbiAgICBpZiAoQXJyYXkuaXNBcnJheShwcm9wVmFsdWUpKSB7XG4gICAgICByZXR1cm4gJ2FycmF5JztcbiAgICB9XG4gICAgaWYgKHByb3BWYWx1ZSBpbnN0YW5jZW9mIFJlZ0V4cCkge1xuICAgICAgLy8gT2xkIHdlYmtpdHMgKGF0IGxlYXN0IHVudGlsIEFuZHJvaWQgNC4wKSByZXR1cm4gJ2Z1bmN0aW9uJyByYXRoZXIgdGhhblxuICAgICAgLy8gJ29iamVjdCcgZm9yIHR5cGVvZiBhIFJlZ0V4cC4gV2UnbGwgbm9ybWFsaXplIHRoaXMgaGVyZSBzbyB0aGF0IC9ibGEvXG4gICAgICAvLyBwYXNzZXMgUHJvcFR5cGVzLm9iamVjdC5cbiAgICAgIHJldHVybiAnb2JqZWN0JztcbiAgICB9XG4gICAgaWYgKGlzU3ltYm9sKHByb3BUeXBlLCBwcm9wVmFsdWUpKSB7XG4gICAgICByZXR1cm4gJ3N5bWJvbCc7XG4gICAgfVxuICAgIHJldHVybiBwcm9wVHlwZTtcbiAgfVxuXG4gIC8vIFRoaXMgaGFuZGxlcyBtb3JlIHR5cGVzIHRoYW4gYGdldFByb3BUeXBlYC4gT25seSB1c2VkIGZvciBlcnJvciBtZXNzYWdlcy5cbiAgLy8gU2VlIGBjcmVhdGVQcmltaXRpdmVUeXBlQ2hlY2tlcmAuXG4gIGZ1bmN0aW9uIGdldFByZWNpc2VUeXBlKHByb3BWYWx1ZSkge1xuICAgIGlmICh0eXBlb2YgcHJvcFZhbHVlID09PSAndW5kZWZpbmVkJyB8fCBwcm9wVmFsdWUgPT09IG51bGwpIHtcbiAgICAgIHJldHVybiAnJyArIHByb3BWYWx1ZTtcbiAgICB9XG4gICAgdmFyIHByb3BUeXBlID0gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKTtcbiAgICBpZiAocHJvcFR5cGUgPT09ICdvYmplY3QnKSB7XG4gICAgICBpZiAocHJvcFZhbHVlIGluc3RhbmNlb2YgRGF0ZSkge1xuICAgICAgICByZXR1cm4gJ2RhdGUnO1xuICAgICAgfSBlbHNlIGlmIChwcm9wVmFsdWUgaW5zdGFuY2VvZiBSZWdFeHApIHtcbiAgICAgICAgcmV0dXJuICdyZWdleHAnO1xuICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gcHJvcFR5cGU7XG4gIH1cblxuICAvLyBSZXR1cm5zIGEgc3RyaW5nIHRoYXQgaXMgcG9zdGZpeGVkIHRvIGEgd2FybmluZyBhYm91dCBhbiBpbnZhbGlkIHR5cGUuXG4gIC8vIEZvciBleGFtcGxlLCBcInVuZGVmaW5lZFwiIG9yIFwib2YgdHlwZSBhcnJheVwiXG4gIGZ1bmN0aW9uIGdldFBvc3RmaXhGb3JUeXBlV2FybmluZyh2YWx1ZSkge1xuICAgIHZhciB0eXBlID0gZ2V0UHJlY2lzZVR5cGUodmFsdWUpO1xuICAgIHN3aXRjaCAodHlwZSkge1xuICAgICAgY2FzZSAnYXJyYXknOlxuICAgICAgY2FzZSAnb2JqZWN0JzpcbiAgICAgICAgcmV0dXJuICdhbiAnICsgdHlwZTtcbiAgICAgIGNhc2UgJ2Jvb2xlYW4nOlxuICAgICAgY2FzZSAnZGF0ZSc6XG4gICAgICBjYXNlICdyZWdleHAnOlxuICAgICAgICByZXR1cm4gJ2EgJyArIHR5cGU7XG4gICAgICBkZWZhdWx0OlxuICAgICAgICByZXR1cm4gdHlwZTtcbiAgICB9XG4gIH1cblxuICAvLyBSZXR1cm5zIGNsYXNzIG5hbWUgb2YgdGhlIG9iamVjdCwgaWYgYW55LlxuICBmdW5jdGlvbiBnZXRDbGFzc05hbWUocHJvcFZhbHVlKSB7XG4gICAgaWYgKCFwcm9wVmFsdWUuY29uc3RydWN0b3IgfHwgIXByb3BWYWx1ZS5jb25zdHJ1Y3Rvci5uYW1lKSB7XG4gICAgICByZXR1cm4gQU5PTllNT1VTO1xuICAgIH1cbiAgICByZXR1cm4gcHJvcFZhbHVlLmNvbnN0cnVjdG9yLm5hbWU7XG4gIH1cblxuICBSZWFjdFByb3BUeXBlcy5jaGVja1Byb3BUeXBlcyA9IGNoZWNrUHJvcFR5cGVzO1xuICBSZWFjdFByb3BUeXBlcy5yZXNldFdhcm5pbmdDYWNoZSA9IGNoZWNrUHJvcFR5cGVzLnJlc2V0V2FybmluZ0NhY2hlO1xuICBSZWFjdFByb3BUeXBlcy5Qcm9wVHlwZXMgPSBSZWFjdFByb3BUeXBlcztcblxuICByZXR1cm4gUmVhY3RQcm9wVHlwZXM7XG59O1xuIiwiLyoqXG4gKiBDb3B5cmlnaHQgKGMpIDIwMTMtcHJlc2VudCwgRmFjZWJvb2ssIEluYy5cbiAqXG4gKiBUaGlzIHNvdXJjZSBjb2RlIGlzIGxpY2Vuc2VkIHVuZGVyIHRoZSBNSVQgbGljZW5zZSBmb3VuZCBpbiB0aGVcbiAqIExJQ0VOU0UgZmlsZSBpbiB0aGUgcm9vdCBkaXJlY3Rvcnkgb2YgdGhpcyBzb3VyY2UgdHJlZS5cbiAqL1xuXG5pZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09ICdwcm9kdWN0aW9uJykge1xuICB2YXIgUmVhY3RJcyA9IHJlcXVpcmUoJ3JlYWN0LWlzJyk7XG5cbiAgLy8gQnkgZXhwbGljaXRseSB1c2luZyBgcHJvcC10eXBlc2AgeW91IGFyZSBvcHRpbmcgaW50byBuZXcgZGV2ZWxvcG1lbnQgYmVoYXZpb3IuXG4gIC8vIGh0dHA6Ly9mYi5tZS9wcm9wLXR5cGVzLWluLXByb2RcbiAgdmFyIHRocm93T25EaXJlY3RBY2Nlc3MgPSB0cnVlO1xuICBtb2R1bGUuZXhwb3J0cyA9IHJlcXVpcmUoJy4vZmFjdG9yeVdpdGhUeXBlQ2hlY2tlcnMnKShSZWFjdElzLmlzRWxlbWVudCwgdGhyb3dPbkRpcmVjdEFjY2Vzcyk7XG59IGVsc2Uge1xuICAvLyBCeSBleHBsaWNpdGx5IHVzaW5nIGBwcm9wLXR5cGVzYCB5b3UgYXJlIG9wdGluZyBpbnRvIG5ldyBwcm9kdWN0aW9uIGJlaGF2aW9yLlxuICAvLyBodHRwOi8vZmIubWUvcHJvcC10eXBlcy1pbi1wcm9kXG4gIG1vZHVsZS5leHBvcnRzID0gcmVxdWlyZSgnLi9mYWN0b3J5V2l0aFRocm93aW5nU2hpbXMnKSgpO1xufVxuIiwiZXhwb3J0IGRlZmF1bHQge1xuICBkaXNhYmxlZDogZmFsc2Vcbn07IiwiaW1wb3J0IFByb3BUeXBlcyBmcm9tICdwcm9wLXR5cGVzJztcbmV4cG9ydCB2YXIgdGltZW91dHNTaGFwZSA9IHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicgPyBQcm9wVHlwZXMub25lT2ZUeXBlKFtQcm9wVHlwZXMubnVtYmVyLCBQcm9wVHlwZXMuc2hhcGUoe1xuICBlbnRlcjogUHJvcFR5cGVzLm51bWJlcixcbiAgZXhpdDogUHJvcFR5cGVzLm51bWJlcixcbiAgYXBwZWFyOiBQcm9wVHlwZXMubnVtYmVyXG59KS5pc1JlcXVpcmVkXSkgOiBudWxsO1xuZXhwb3J0IHZhciBjbGFzc05hbWVzU2hhcGUgPSBwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gJ3Byb2R1Y3Rpb24nID8gUHJvcFR5cGVzLm9uZU9mVHlwZShbUHJvcFR5cGVzLnN0cmluZywgUHJvcFR5cGVzLnNoYXBlKHtcbiAgZW50ZXI6IFByb3BUeXBlcy5zdHJpbmcsXG4gIGV4aXQ6IFByb3BUeXBlcy5zdHJpbmcsXG4gIGFjdGl2ZTogUHJvcFR5cGVzLnN0cmluZ1xufSksIFByb3BUeXBlcy5zaGFwZSh7XG4gIGVudGVyOiBQcm9wVHlwZXMuc3RyaW5nLFxuICBlbnRlckRvbmU6IFByb3BUeXBlcy5zdHJpbmcsXG4gIGVudGVyQWN0aXZlOiBQcm9wVHlwZXMuc3RyaW5nLFxuICBleGl0OiBQcm9wVHlwZXMuc3RyaW5nLFxuICBleGl0RG9uZTogUHJvcFR5cGVzLnN0cmluZyxcbiAgZXhpdEFjdGl2ZTogUHJvcFR5cGVzLnN0cmluZ1xufSldKSA6IG51bGw7IiwiaW1wb3J0IFJlYWN0IGZyb20gJ3JlYWN0JztcbmV4cG9ydCBkZWZhdWx0IFJlYWN0LmNyZWF0ZUNvbnRleHQobnVsbCk7IiwiZXhwb3J0IHZhciBmb3JjZVJlZmxvdyA9IGZ1bmN0aW9uIGZvcmNlUmVmbG93KG5vZGUpIHtcbiAgcmV0dXJuIG5vZGUuc2Nyb2xsVG9wO1xufTsiLCJpbXBvcnQgX29iamVjdFdpdGhvdXRQcm9wZXJ0aWVzTG9vc2UgZnJvbSBcIkBiYWJlbC9ydW50aW1lL2hlbHBlcnMvZXNtL29iamVjdFdpdGhvdXRQcm9wZXJ0aWVzTG9vc2VcIjtcbmltcG9ydCBfaW5oZXJpdHNMb29zZSBmcm9tIFwiQGJhYmVsL3J1bnRpbWUvaGVscGVycy9lc20vaW5oZXJpdHNMb29zZVwiO1xuaW1wb3J0IFByb3BUeXBlcyBmcm9tICdwcm9wLXR5cGVzJztcbmltcG9ydCBSZWFjdCBmcm9tICdyZWFjdCc7XG5pbXBvcnQgUmVhY3RET00gZnJvbSAncmVhY3QtZG9tJztcbmltcG9ydCBjb25maWcgZnJvbSAnLi9jb25maWcnO1xuaW1wb3J0IHsgdGltZW91dHNTaGFwZSB9IGZyb20gJy4vdXRpbHMvUHJvcFR5cGVzJztcbmltcG9ydCBUcmFuc2l0aW9uR3JvdXBDb250ZXh0IGZyb20gJy4vVHJhbnNpdGlvbkdyb3VwQ29udGV4dCc7XG5pbXBvcnQgeyBmb3JjZVJlZmxvdyB9IGZyb20gJy4vdXRpbHMvcmVmbG93JztcbmV4cG9ydCB2YXIgVU5NT1VOVEVEID0gJ3VubW91bnRlZCc7XG5leHBvcnQgdmFyIEVYSVRFRCA9ICdleGl0ZWQnO1xuZXhwb3J0IHZhciBFTlRFUklORyA9ICdlbnRlcmluZyc7XG5leHBvcnQgdmFyIEVOVEVSRUQgPSAnZW50ZXJlZCc7XG5leHBvcnQgdmFyIEVYSVRJTkcgPSAnZXhpdGluZyc7XG4vKipcbiAqIFRoZSBUcmFuc2l0aW9uIGNvbXBvbmVudCBsZXRzIHlvdSBkZXNjcmliZSBhIHRyYW5zaXRpb24gZnJvbSBvbmUgY29tcG9uZW50XG4gKiBzdGF0ZSB0byBhbm90aGVyIF9vdmVyIHRpbWVfIHdpdGggYSBzaW1wbGUgZGVjbGFyYXRpdmUgQVBJLiBNb3N0IGNvbW1vbmx5XG4gKiBpdCdzIHVzZWQgdG8gYW5pbWF0ZSB0aGUgbW91bnRpbmcgYW5kIHVubW91bnRpbmcgb2YgYSBjb21wb25lbnQsIGJ1dCBjYW4gYWxzb1xuICogYmUgdXNlZCB0byBkZXNjcmliZSBpbi1wbGFjZSB0cmFuc2l0aW9uIHN0YXRlcyBhcyB3ZWxsLlxuICpcbiAqIC0tLVxuICpcbiAqICoqTm90ZSoqOiBgVHJhbnNpdGlvbmAgaXMgYSBwbGF0Zm9ybS1hZ25vc3RpYyBiYXNlIGNvbXBvbmVudC4gSWYgeW91J3JlIHVzaW5nXG4gKiB0cmFuc2l0aW9ucyBpbiBDU1MsIHlvdSdsbCBwcm9iYWJseSB3YW50IHRvIHVzZVxuICogW2BDU1NUcmFuc2l0aW9uYF0oaHR0cHM6Ly9yZWFjdGNvbW11bml0eS5vcmcvcmVhY3QtdHJhbnNpdGlvbi1ncm91cC9jc3MtdHJhbnNpdGlvbilcbiAqIGluc3RlYWQuIEl0IGluaGVyaXRzIGFsbCB0aGUgZmVhdHVyZXMgb2YgYFRyYW5zaXRpb25gLCBidXQgY29udGFpbnNcbiAqIGFkZGl0aW9uYWwgZmVhdHVyZXMgbmVjZXNzYXJ5IHRvIHBsYXkgbmljZSB3aXRoIENTUyB0cmFuc2l0aW9ucyAoaGVuY2UgdGhlXG4gKiBuYW1lIG9mIHRoZSBjb21wb25lbnQpLlxuICpcbiAqIC0tLVxuICpcbiAqIEJ5IGRlZmF1bHQgdGhlIGBUcmFuc2l0aW9uYCBjb21wb25lbnQgZG9lcyBub3QgYWx0ZXIgdGhlIGJlaGF2aW9yIG9mIHRoZVxuICogY29tcG9uZW50IGl0IHJlbmRlcnMsIGl0IG9ubHkgdHJhY2tzIFwiZW50ZXJcIiBhbmQgXCJleGl0XCIgc3RhdGVzIGZvciB0aGVcbiAqIGNvbXBvbmVudHMuIEl0J3MgdXAgdG8geW91IHRvIGdpdmUgbWVhbmluZyBhbmQgZWZmZWN0IHRvIHRob3NlIHN0YXRlcy4gRm9yXG4gKiBleGFtcGxlIHdlIGNhbiBhZGQgc3R5bGVzIHRvIGEgY29tcG9uZW50IHdoZW4gaXQgZW50ZXJzIG9yIGV4aXRzOlxuICpcbiAqIGBgYGpzeFxuICogaW1wb3J0IHsgVHJhbnNpdGlvbiB9IGZyb20gJ3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAnO1xuICpcbiAqIGNvbnN0IGR1cmF0aW9uID0gMzAwO1xuICpcbiAqIGNvbnN0IGRlZmF1bHRTdHlsZSA9IHtcbiAqICAgdHJhbnNpdGlvbjogYG9wYWNpdHkgJHtkdXJhdGlvbn1tcyBlYXNlLWluLW91dGAsXG4gKiAgIG9wYWNpdHk6IDAsXG4gKiB9XG4gKlxuICogY29uc3QgdHJhbnNpdGlvblN0eWxlcyA9IHtcbiAqICAgZW50ZXJpbmc6IHsgb3BhY2l0eTogMSB9LFxuICogICBlbnRlcmVkOiAgeyBvcGFjaXR5OiAxIH0sXG4gKiAgIGV4aXRpbmc6ICB7IG9wYWNpdHk6IDAgfSxcbiAqICAgZXhpdGVkOiAgeyBvcGFjaXR5OiAwIH0sXG4gKiB9O1xuICpcbiAqIGNvbnN0IEZhZGUgPSAoeyBpbjogaW5Qcm9wIH0pID0+IChcbiAqICAgPFRyYW5zaXRpb24gaW49e2luUHJvcH0gdGltZW91dD17ZHVyYXRpb259PlxuICogICAgIHtzdGF0ZSA9PiAoXG4gKiAgICAgICA8ZGl2IHN0eWxlPXt7XG4gKiAgICAgICAgIC4uLmRlZmF1bHRTdHlsZSxcbiAqICAgICAgICAgLi4udHJhbnNpdGlvblN0eWxlc1tzdGF0ZV1cbiAqICAgICAgIH19PlxuICogICAgICAgICBJJ20gYSBmYWRlIFRyYW5zaXRpb24hXG4gKiAgICAgICA8L2Rpdj5cbiAqICAgICApfVxuICogICA8L1RyYW5zaXRpb24+XG4gKiApO1xuICogYGBgXG4gKlxuICogVGhlcmUgYXJlIDQgbWFpbiBzdGF0ZXMgYSBUcmFuc2l0aW9uIGNhbiBiZSBpbjpcbiAqICAtIGAnZW50ZXJpbmcnYFxuICogIC0gYCdlbnRlcmVkJ2BcbiAqICAtIGAnZXhpdGluZydgXG4gKiAgLSBgJ2V4aXRlZCdgXG4gKlxuICogVHJhbnNpdGlvbiBzdGF0ZSBpcyB0b2dnbGVkIHZpYSB0aGUgYGluYCBwcm9wLiBXaGVuIGB0cnVlYCB0aGUgY29tcG9uZW50XG4gKiBiZWdpbnMgdGhlIFwiRW50ZXJcIiBzdGFnZS4gRHVyaW5nIHRoaXMgc3RhZ2UsIHRoZSBjb21wb25lbnQgd2lsbCBzaGlmdCBmcm9tXG4gKiBpdHMgY3VycmVudCB0cmFuc2l0aW9uIHN0YXRlLCB0byBgJ2VudGVyaW5nJ2AgZm9yIHRoZSBkdXJhdGlvbiBvZiB0aGVcbiAqIHRyYW5zaXRpb24gYW5kIHRoZW4gdG8gdGhlIGAnZW50ZXJlZCdgIHN0YWdlIG9uY2UgaXQncyBjb21wbGV0ZS4gTGV0J3MgdGFrZVxuICogdGhlIGZvbGxvd2luZyBleGFtcGxlICh3ZSdsbCB1c2UgdGhlXG4gKiBbdXNlU3RhdGVdKGh0dHBzOi8vcmVhY3Rqcy5vcmcvZG9jcy9ob29rcy1yZWZlcmVuY2UuaHRtbCN1c2VzdGF0ZSkgaG9vayk6XG4gKlxuICogYGBganN4XG4gKiBmdW5jdGlvbiBBcHAoKSB7XG4gKiAgIGNvbnN0IFtpblByb3AsIHNldEluUHJvcF0gPSB1c2VTdGF0ZShmYWxzZSk7XG4gKiAgIHJldHVybiAoXG4gKiAgICAgPGRpdj5cbiAqICAgICAgIDxUcmFuc2l0aW9uIGluPXtpblByb3B9IHRpbWVvdXQ9ezUwMH0+XG4gKiAgICAgICAgIHtzdGF0ZSA9PiAoXG4gKiAgICAgICAgICAgLy8gLi4uXG4gKiAgICAgICAgICl9XG4gKiAgICAgICA8L1RyYW5zaXRpb24+XG4gKiAgICAgICA8YnV0dG9uIG9uQ2xpY2s9eygpID0+IHNldEluUHJvcCh0cnVlKX0+XG4gKiAgICAgICAgIENsaWNrIHRvIEVudGVyXG4gKiAgICAgICA8L2J1dHRvbj5cbiAqICAgICA8L2Rpdj5cbiAqICAgKTtcbiAqIH1cbiAqIGBgYFxuICpcbiAqIFdoZW4gdGhlIGJ1dHRvbiBpcyBjbGlja2VkIHRoZSBjb21wb25lbnQgd2lsbCBzaGlmdCB0byB0aGUgYCdlbnRlcmluZydgIHN0YXRlXG4gKiBhbmQgc3RheSB0aGVyZSBmb3IgNTAwbXMgKHRoZSB2YWx1ZSBvZiBgdGltZW91dGApIGJlZm9yZSBpdCBmaW5hbGx5IHN3aXRjaGVzXG4gKiB0byBgJ2VudGVyZWQnYC5cbiAqXG4gKiBXaGVuIGBpbmAgaXMgYGZhbHNlYCB0aGUgc2FtZSB0aGluZyBoYXBwZW5zIGV4Y2VwdCB0aGUgc3RhdGUgbW92ZXMgZnJvbVxuICogYCdleGl0aW5nJ2AgdG8gYCdleGl0ZWQnYC5cbiAqL1xuXG52YXIgVHJhbnNpdGlvbiA9IC8qI19fUFVSRV9fKi9mdW5jdGlvbiAoX1JlYWN0JENvbXBvbmVudCkge1xuICBfaW5oZXJpdHNMb29zZShUcmFuc2l0aW9uLCBfUmVhY3QkQ29tcG9uZW50KTtcblxuICBmdW5jdGlvbiBUcmFuc2l0aW9uKHByb3BzLCBjb250ZXh0KSB7XG4gICAgdmFyIF90aGlzO1xuXG4gICAgX3RoaXMgPSBfUmVhY3QkQ29tcG9uZW50LmNhbGwodGhpcywgcHJvcHMsIGNvbnRleHQpIHx8IHRoaXM7XG4gICAgdmFyIHBhcmVudEdyb3VwID0gY29udGV4dDsgLy8gSW4gdGhlIGNvbnRleHQgb2YgYSBUcmFuc2l0aW9uR3JvdXAgYWxsIGVudGVycyBhcmUgcmVhbGx5IGFwcGVhcnNcblxuICAgIHZhciBhcHBlYXIgPSBwYXJlbnRHcm91cCAmJiAhcGFyZW50R3JvdXAuaXNNb3VudGluZyA/IHByb3BzLmVudGVyIDogcHJvcHMuYXBwZWFyO1xuICAgIHZhciBpbml0aWFsU3RhdHVzO1xuICAgIF90aGlzLmFwcGVhclN0YXR1cyA9IG51bGw7XG5cbiAgICBpZiAocHJvcHMuaW4pIHtcbiAgICAgIGlmIChhcHBlYXIpIHtcbiAgICAgICAgaW5pdGlhbFN0YXR1cyA9IEVYSVRFRDtcbiAgICAgICAgX3RoaXMuYXBwZWFyU3RhdHVzID0gRU5URVJJTkc7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpbml0aWFsU3RhdHVzID0gRU5URVJFRDtcbiAgICAgIH1cbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKHByb3BzLnVubW91bnRPbkV4aXQgfHwgcHJvcHMubW91bnRPbkVudGVyKSB7XG4gICAgICAgIGluaXRpYWxTdGF0dXMgPSBVTk1PVU5URUQ7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpbml0aWFsU3RhdHVzID0gRVhJVEVEO1xuICAgICAgfVxuICAgIH1cblxuICAgIF90aGlzLnN0YXRlID0ge1xuICAgICAgc3RhdHVzOiBpbml0aWFsU3RhdHVzXG4gICAgfTtcbiAgICBfdGhpcy5uZXh0Q2FsbGJhY2sgPSBudWxsO1xuICAgIHJldHVybiBfdGhpcztcbiAgfVxuXG4gIFRyYW5zaXRpb24uZ2V0RGVyaXZlZFN0YXRlRnJvbVByb3BzID0gZnVuY3Rpb24gZ2V0RGVyaXZlZFN0YXRlRnJvbVByb3BzKF9yZWYsIHByZXZTdGF0ZSkge1xuICAgIHZhciBuZXh0SW4gPSBfcmVmLmluO1xuXG4gICAgaWYgKG5leHRJbiAmJiBwcmV2U3RhdGUuc3RhdHVzID09PSBVTk1PVU5URUQpIHtcbiAgICAgIHJldHVybiB7XG4gICAgICAgIHN0YXR1czogRVhJVEVEXG4gICAgICB9O1xuICAgIH1cblxuICAgIHJldHVybiBudWxsO1xuICB9IC8vIGdldFNuYXBzaG90QmVmb3JlVXBkYXRlKHByZXZQcm9wcykge1xuICAvLyAgIGxldCBuZXh0U3RhdHVzID0gbnVsbFxuICAvLyAgIGlmIChwcmV2UHJvcHMgIT09IHRoaXMucHJvcHMpIHtcbiAgLy8gICAgIGNvbnN0IHsgc3RhdHVzIH0gPSB0aGlzLnN0YXRlXG4gIC8vICAgICBpZiAodGhpcy5wcm9wcy5pbikge1xuICAvLyAgICAgICBpZiAoc3RhdHVzICE9PSBFTlRFUklORyAmJiBzdGF0dXMgIT09IEVOVEVSRUQpIHtcbiAgLy8gICAgICAgICBuZXh0U3RhdHVzID0gRU5URVJJTkdcbiAgLy8gICAgICAgfVxuICAvLyAgICAgfSBlbHNlIHtcbiAgLy8gICAgICAgaWYgKHN0YXR1cyA9PT0gRU5URVJJTkcgfHwgc3RhdHVzID09PSBFTlRFUkVEKSB7XG4gIC8vICAgICAgICAgbmV4dFN0YXR1cyA9IEVYSVRJTkdcbiAgLy8gICAgICAgfVxuICAvLyAgICAgfVxuICAvLyAgIH1cbiAgLy8gICByZXR1cm4geyBuZXh0U3RhdHVzIH1cbiAgLy8gfVxuICA7XG5cbiAgdmFyIF9wcm90byA9IFRyYW5zaXRpb24ucHJvdG90eXBlO1xuXG4gIF9wcm90by5jb21wb25lbnREaWRNb3VudCA9IGZ1bmN0aW9uIGNvbXBvbmVudERpZE1vdW50KCkge1xuICAgIHRoaXMudXBkYXRlU3RhdHVzKHRydWUsIHRoaXMuYXBwZWFyU3RhdHVzKTtcbiAgfTtcblxuICBfcHJvdG8uY29tcG9uZW50RGlkVXBkYXRlID0gZnVuY3Rpb24gY29tcG9uZW50RGlkVXBkYXRlKHByZXZQcm9wcykge1xuICAgIHZhciBuZXh0U3RhdHVzID0gbnVsbDtcblxuICAgIGlmIChwcmV2UHJvcHMgIT09IHRoaXMucHJvcHMpIHtcbiAgICAgIHZhciBzdGF0dXMgPSB0aGlzLnN0YXRlLnN0YXR1cztcblxuICAgICAgaWYgKHRoaXMucHJvcHMuaW4pIHtcbiAgICAgICAgaWYgKHN0YXR1cyAhPT0gRU5URVJJTkcgJiYgc3RhdHVzICE9PSBFTlRFUkVEKSB7XG4gICAgICAgICAgbmV4dFN0YXR1cyA9IEVOVEVSSU5HO1xuICAgICAgICB9XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBpZiAoc3RhdHVzID09PSBFTlRFUklORyB8fCBzdGF0dXMgPT09IEVOVEVSRUQpIHtcbiAgICAgICAgICBuZXh0U3RhdHVzID0gRVhJVElORztcbiAgICAgICAgfVxuICAgICAgfVxuICAgIH1cblxuICAgIHRoaXMudXBkYXRlU3RhdHVzKGZhbHNlLCBuZXh0U3RhdHVzKTtcbiAgfTtcblxuICBfcHJvdG8uY29tcG9uZW50V2lsbFVubW91bnQgPSBmdW5jdGlvbiBjb21wb25lbnRXaWxsVW5tb3VudCgpIHtcbiAgICB0aGlzLmNhbmNlbE5leHRDYWxsYmFjaygpO1xuICB9O1xuXG4gIF9wcm90by5nZXRUaW1lb3V0cyA9IGZ1bmN0aW9uIGdldFRpbWVvdXRzKCkge1xuICAgIHZhciB0aW1lb3V0ID0gdGhpcy5wcm9wcy50aW1lb3V0O1xuICAgIHZhciBleGl0LCBlbnRlciwgYXBwZWFyO1xuICAgIGV4aXQgPSBlbnRlciA9IGFwcGVhciA9IHRpbWVvdXQ7XG5cbiAgICBpZiAodGltZW91dCAhPSBudWxsICYmIHR5cGVvZiB0aW1lb3V0ICE9PSAnbnVtYmVyJykge1xuICAgICAgZXhpdCA9IHRpbWVvdXQuZXhpdDtcbiAgICAgIGVudGVyID0gdGltZW91dC5lbnRlcjsgLy8gVE9ETzogcmVtb3ZlIGZhbGxiYWNrIGZvciBuZXh0IG1ham9yXG5cbiAgICAgIGFwcGVhciA9IHRpbWVvdXQuYXBwZWFyICE9PSB1bmRlZmluZWQgPyB0aW1lb3V0LmFwcGVhciA6IGVudGVyO1xuICAgIH1cblxuICAgIHJldHVybiB7XG4gICAgICBleGl0OiBleGl0LFxuICAgICAgZW50ZXI6IGVudGVyLFxuICAgICAgYXBwZWFyOiBhcHBlYXJcbiAgICB9O1xuICB9O1xuXG4gIF9wcm90by51cGRhdGVTdGF0dXMgPSBmdW5jdGlvbiB1cGRhdGVTdGF0dXMobW91bnRpbmcsIG5leHRTdGF0dXMpIHtcbiAgICBpZiAobW91bnRpbmcgPT09IHZvaWQgMCkge1xuICAgICAgbW91bnRpbmcgPSBmYWxzZTtcbiAgICB9XG5cbiAgICBpZiAobmV4dFN0YXR1cyAhPT0gbnVsbCkge1xuICAgICAgLy8gbmV4dFN0YXR1cyB3aWxsIGFsd2F5cyBiZSBFTlRFUklORyBvciBFWElUSU5HLlxuICAgICAgdGhpcy5jYW5jZWxOZXh0Q2FsbGJhY2soKTtcblxuICAgICAgaWYgKG5leHRTdGF0dXMgPT09IEVOVEVSSU5HKSB7XG4gICAgICAgIGlmICh0aGlzLnByb3BzLnVubW91bnRPbkV4aXQgfHwgdGhpcy5wcm9wcy5tb3VudE9uRW50ZXIpIHtcbiAgICAgICAgICB2YXIgbm9kZSA9IHRoaXMucHJvcHMubm9kZVJlZiA/IHRoaXMucHJvcHMubm9kZVJlZi5jdXJyZW50IDogUmVhY3RET00uZmluZERPTU5vZGUodGhpcyk7IC8vIGh0dHBzOi8vZ2l0aHViLmNvbS9yZWFjdGpzL3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvcHVsbC83NDlcbiAgICAgICAgICAvLyBXaXRoIHVubW91bnRPbkV4aXQgb3IgbW91bnRPbkVudGVyLCB0aGUgZW50ZXIgYW5pbWF0aW9uIHNob3VsZCBoYXBwZW4gYXQgdGhlIHRyYW5zaXRpb24gYmV0d2VlbiBgZXhpdGVkYCBhbmQgYGVudGVyaW5nYC5cbiAgICAgICAgICAvLyBUbyBtYWtlIHRoZSBhbmltYXRpb24gaGFwcGVuLCAgd2UgaGF2ZSB0byBzZXBhcmF0ZSBlYWNoIHJlbmRlcmluZyBhbmQgYXZvaWQgYmVpbmcgcHJvY2Vzc2VkIGFzIGJhdGNoZWQuXG5cbiAgICAgICAgICBpZiAobm9kZSkgZm9yY2VSZWZsb3cobm9kZSk7XG4gICAgICAgIH1cblxuICAgICAgICB0aGlzLnBlcmZvcm1FbnRlcihtb3VudGluZyk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICB0aGlzLnBlcmZvcm1FeGl0KCk7XG4gICAgICB9XG4gICAgfSBlbHNlIGlmICh0aGlzLnByb3BzLnVubW91bnRPbkV4aXQgJiYgdGhpcy5zdGF0ZS5zdGF0dXMgPT09IEVYSVRFRCkge1xuICAgICAgdGhpcy5zZXRTdGF0ZSh7XG4gICAgICAgIHN0YXR1czogVU5NT1VOVEVEXG4gICAgICB9KTtcbiAgICB9XG4gIH07XG5cbiAgX3Byb3RvLnBlcmZvcm1FbnRlciA9IGZ1bmN0aW9uIHBlcmZvcm1FbnRlcihtb3VudGluZykge1xuICAgIHZhciBfdGhpczIgPSB0aGlzO1xuXG4gICAgdmFyIGVudGVyID0gdGhpcy5wcm9wcy5lbnRlcjtcbiAgICB2YXIgYXBwZWFyaW5nID0gdGhpcy5jb250ZXh0ID8gdGhpcy5jb250ZXh0LmlzTW91bnRpbmcgOiBtb3VudGluZztcblxuICAgIHZhciBfcmVmMiA9IHRoaXMucHJvcHMubm9kZVJlZiA/IFthcHBlYXJpbmddIDogW1JlYWN0RE9NLmZpbmRET01Ob2RlKHRoaXMpLCBhcHBlYXJpbmddLFxuICAgICAgICBtYXliZU5vZGUgPSBfcmVmMlswXSxcbiAgICAgICAgbWF5YmVBcHBlYXJpbmcgPSBfcmVmMlsxXTtcblxuICAgIHZhciB0aW1lb3V0cyA9IHRoaXMuZ2V0VGltZW91dHMoKTtcbiAgICB2YXIgZW50ZXJUaW1lb3V0ID0gYXBwZWFyaW5nID8gdGltZW91dHMuYXBwZWFyIDogdGltZW91dHMuZW50ZXI7IC8vIG5vIGVudGVyIGFuaW1hdGlvbiBza2lwIHJpZ2h0IHRvIEVOVEVSRURcbiAgICAvLyBpZiB3ZSBhcmUgbW91bnRpbmcgYW5kIHJ1bm5pbmcgdGhpcyBpdCBtZWFucyBhcHBlYXIgX211c3RfIGJlIHNldFxuXG4gICAgaWYgKCFtb3VudGluZyAmJiAhZW50ZXIgfHwgY29uZmlnLmRpc2FibGVkKSB7XG4gICAgICB0aGlzLnNhZmVTZXRTdGF0ZSh7XG4gICAgICAgIHN0YXR1czogRU5URVJFRFxuICAgICAgfSwgZnVuY3Rpb24gKCkge1xuICAgICAgICBfdGhpczIucHJvcHMub25FbnRlcmVkKG1heWJlTm9kZSk7XG4gICAgICB9KTtcbiAgICAgIHJldHVybjtcbiAgICB9XG5cbiAgICB0aGlzLnByb3BzLm9uRW50ZXIobWF5YmVOb2RlLCBtYXliZUFwcGVhcmluZyk7XG4gICAgdGhpcy5zYWZlU2V0U3RhdGUoe1xuICAgICAgc3RhdHVzOiBFTlRFUklOR1xuICAgIH0sIGZ1bmN0aW9uICgpIHtcbiAgICAgIF90aGlzMi5wcm9wcy5vbkVudGVyaW5nKG1heWJlTm9kZSwgbWF5YmVBcHBlYXJpbmcpO1xuXG4gICAgICBfdGhpczIub25UcmFuc2l0aW9uRW5kKGVudGVyVGltZW91dCwgZnVuY3Rpb24gKCkge1xuICAgICAgICBfdGhpczIuc2FmZVNldFN0YXRlKHtcbiAgICAgICAgICBzdGF0dXM6IEVOVEVSRURcbiAgICAgICAgfSwgZnVuY3Rpb24gKCkge1xuICAgICAgICAgIF90aGlzMi5wcm9wcy5vbkVudGVyZWQobWF5YmVOb2RlLCBtYXliZUFwcGVhcmluZyk7XG4gICAgICAgIH0pO1xuICAgICAgfSk7XG4gICAgfSk7XG4gIH07XG5cbiAgX3Byb3RvLnBlcmZvcm1FeGl0ID0gZnVuY3Rpb24gcGVyZm9ybUV4aXQoKSB7XG4gICAgdmFyIF90aGlzMyA9IHRoaXM7XG5cbiAgICB2YXIgZXhpdCA9IHRoaXMucHJvcHMuZXhpdDtcbiAgICB2YXIgdGltZW91dHMgPSB0aGlzLmdldFRpbWVvdXRzKCk7XG4gICAgdmFyIG1heWJlTm9kZSA9IHRoaXMucHJvcHMubm9kZVJlZiA/IHVuZGVmaW5lZCA6IFJlYWN0RE9NLmZpbmRET01Ob2RlKHRoaXMpOyAvLyBubyBleGl0IGFuaW1hdGlvbiBza2lwIHJpZ2h0IHRvIEVYSVRFRFxuXG4gICAgaWYgKCFleGl0IHx8IGNvbmZpZy5kaXNhYmxlZCkge1xuICAgICAgdGhpcy5zYWZlU2V0U3RhdGUoe1xuICAgICAgICBzdGF0dXM6IEVYSVRFRFxuICAgICAgfSwgZnVuY3Rpb24gKCkge1xuICAgICAgICBfdGhpczMucHJvcHMub25FeGl0ZWQobWF5YmVOb2RlKTtcbiAgICAgIH0pO1xuICAgICAgcmV0dXJuO1xuICAgIH1cblxuICAgIHRoaXMucHJvcHMub25FeGl0KG1heWJlTm9kZSk7XG4gICAgdGhpcy5zYWZlU2V0U3RhdGUoe1xuICAgICAgc3RhdHVzOiBFWElUSU5HXG4gICAgfSwgZnVuY3Rpb24gKCkge1xuICAgICAgX3RoaXMzLnByb3BzLm9uRXhpdGluZyhtYXliZU5vZGUpO1xuXG4gICAgICBfdGhpczMub25UcmFuc2l0aW9uRW5kKHRpbWVvdXRzLmV4aXQsIGZ1bmN0aW9uICgpIHtcbiAgICAgICAgX3RoaXMzLnNhZmVTZXRTdGF0ZSh7XG4gICAgICAgICAgc3RhdHVzOiBFWElURURcbiAgICAgICAgfSwgZnVuY3Rpb24gKCkge1xuICAgICAgICAgIF90aGlzMy5wcm9wcy5vbkV4aXRlZChtYXliZU5vZGUpO1xuICAgICAgICB9KTtcbiAgICAgIH0pO1xuICAgIH0pO1xuICB9O1xuXG4gIF9wcm90by5jYW5jZWxOZXh0Q2FsbGJhY2sgPSBmdW5jdGlvbiBjYW5jZWxOZXh0Q2FsbGJhY2soKSB7XG4gICAgaWYgKHRoaXMubmV4dENhbGxiYWNrICE9PSBudWxsKSB7XG4gICAgICB0aGlzLm5leHRDYWxsYmFjay5jYW5jZWwoKTtcbiAgICAgIHRoaXMubmV4dENhbGxiYWNrID0gbnVsbDtcbiAgICB9XG4gIH07XG5cbiAgX3Byb3RvLnNhZmVTZXRTdGF0ZSA9IGZ1bmN0aW9uIHNhZmVTZXRTdGF0ZShuZXh0U3RhdGUsIGNhbGxiYWNrKSB7XG4gICAgLy8gVGhpcyBzaG91bGRuJ3QgYmUgbmVjZXNzYXJ5LCBidXQgdGhlcmUgYXJlIHdlaXJkIHJhY2UgY29uZGl0aW9ucyB3aXRoXG4gICAgLy8gc2V0U3RhdGUgY2FsbGJhY2tzIGFuZCB1bm1vdW50aW5nIGluIHRlc3RpbmcsIHNvIGFsd2F5cyBtYWtlIHN1cmUgdGhhdFxuICAgIC8vIHdlIGNhbiBjYW5jZWwgYW55IHBlbmRpbmcgc2V0U3RhdGUgY2FsbGJhY2tzIGFmdGVyIHdlIHVubW91bnQuXG4gICAgY2FsbGJhY2sgPSB0aGlzLnNldE5leHRDYWxsYmFjayhjYWxsYmFjayk7XG4gICAgdGhpcy5zZXRTdGF0ZShuZXh0U3RhdGUsIGNhbGxiYWNrKTtcbiAgfTtcblxuICBfcHJvdG8uc2V0TmV4dENhbGxiYWNrID0gZnVuY3Rpb24gc2V0TmV4dENhbGxiYWNrKGNhbGxiYWNrKSB7XG4gICAgdmFyIF90aGlzNCA9IHRoaXM7XG5cbiAgICB2YXIgYWN0aXZlID0gdHJ1ZTtcblxuICAgIHRoaXMubmV4dENhbGxiYWNrID0gZnVuY3Rpb24gKGV2ZW50KSB7XG4gICAgICBpZiAoYWN0aXZlKSB7XG4gICAgICAgIGFjdGl2ZSA9IGZhbHNlO1xuICAgICAgICBfdGhpczQubmV4dENhbGxiYWNrID0gbnVsbDtcbiAgICAgICAgY2FsbGJhY2soZXZlbnQpO1xuICAgICAgfVxuICAgIH07XG5cbiAgICB0aGlzLm5leHRDYWxsYmFjay5jYW5jZWwgPSBmdW5jdGlvbiAoKSB7XG4gICAgICBhY3RpdmUgPSBmYWxzZTtcbiAgICB9O1xuXG4gICAgcmV0dXJuIHRoaXMubmV4dENhbGxiYWNrO1xuICB9O1xuXG4gIF9wcm90by5vblRyYW5zaXRpb25FbmQgPSBmdW5jdGlvbiBvblRyYW5zaXRpb25FbmQodGltZW91dCwgaGFuZGxlcikge1xuICAgIHRoaXMuc2V0TmV4dENhbGxiYWNrKGhhbmRsZXIpO1xuICAgIHZhciBub2RlID0gdGhpcy5wcm9wcy5ub2RlUmVmID8gdGhpcy5wcm9wcy5ub2RlUmVmLmN1cnJlbnQgOiBSZWFjdERPTS5maW5kRE9NTm9kZSh0aGlzKTtcbiAgICB2YXIgZG9lc05vdEhhdmVUaW1lb3V0T3JMaXN0ZW5lciA9IHRpbWVvdXQgPT0gbnVsbCAmJiAhdGhpcy5wcm9wcy5hZGRFbmRMaXN0ZW5lcjtcblxuICAgIGlmICghbm9kZSB8fCBkb2VzTm90SGF2ZVRpbWVvdXRPckxpc3RlbmVyKSB7XG4gICAgICBzZXRUaW1lb3V0KHRoaXMubmV4dENhbGxiYWNrLCAwKTtcbiAgICAgIHJldHVybjtcbiAgICB9XG5cbiAgICBpZiAodGhpcy5wcm9wcy5hZGRFbmRMaXN0ZW5lcikge1xuICAgICAgdmFyIF9yZWYzID0gdGhpcy5wcm9wcy5ub2RlUmVmID8gW3RoaXMubmV4dENhbGxiYWNrXSA6IFtub2RlLCB0aGlzLm5leHRDYWxsYmFja10sXG4gICAgICAgICAgbWF5YmVOb2RlID0gX3JlZjNbMF0sXG4gICAgICAgICAgbWF5YmVOZXh0Q2FsbGJhY2sgPSBfcmVmM1sxXTtcblxuICAgICAgdGhpcy5wcm9wcy5hZGRFbmRMaXN0ZW5lcihtYXliZU5vZGUsIG1heWJlTmV4dENhbGxiYWNrKTtcbiAgICB9XG5cbiAgICBpZiAodGltZW91dCAhPSBudWxsKSB7XG4gICAgICBzZXRUaW1lb3V0KHRoaXMubmV4dENhbGxiYWNrLCB0aW1lb3V0KTtcbiAgICB9XG4gIH07XG5cbiAgX3Byb3RvLnJlbmRlciA9IGZ1bmN0aW9uIHJlbmRlcigpIHtcbiAgICB2YXIgc3RhdHVzID0gdGhpcy5zdGF0ZS5zdGF0dXM7XG5cbiAgICBpZiAoc3RhdHVzID09PSBVTk1PVU5URUQpIHtcbiAgICAgIHJldHVybiBudWxsO1xuICAgIH1cblxuICAgIHZhciBfdGhpcyRwcm9wcyA9IHRoaXMucHJvcHMsXG4gICAgICAgIGNoaWxkcmVuID0gX3RoaXMkcHJvcHMuY2hpbGRyZW4sXG4gICAgICAgIF9pbiA9IF90aGlzJHByb3BzLmluLFxuICAgICAgICBfbW91bnRPbkVudGVyID0gX3RoaXMkcHJvcHMubW91bnRPbkVudGVyLFxuICAgICAgICBfdW5tb3VudE9uRXhpdCA9IF90aGlzJHByb3BzLnVubW91bnRPbkV4aXQsXG4gICAgICAgIF9hcHBlYXIgPSBfdGhpcyRwcm9wcy5hcHBlYXIsXG4gICAgICAgIF9lbnRlciA9IF90aGlzJHByb3BzLmVudGVyLFxuICAgICAgICBfZXhpdCA9IF90aGlzJHByb3BzLmV4aXQsXG4gICAgICAgIF90aW1lb3V0ID0gX3RoaXMkcHJvcHMudGltZW91dCxcbiAgICAgICAgX2FkZEVuZExpc3RlbmVyID0gX3RoaXMkcHJvcHMuYWRkRW5kTGlzdGVuZXIsXG4gICAgICAgIF9vbkVudGVyID0gX3RoaXMkcHJvcHMub25FbnRlcixcbiAgICAgICAgX29uRW50ZXJpbmcgPSBfdGhpcyRwcm9wcy5vbkVudGVyaW5nLFxuICAgICAgICBfb25FbnRlcmVkID0gX3RoaXMkcHJvcHMub25FbnRlcmVkLFxuICAgICAgICBfb25FeGl0ID0gX3RoaXMkcHJvcHMub25FeGl0LFxuICAgICAgICBfb25FeGl0aW5nID0gX3RoaXMkcHJvcHMub25FeGl0aW5nLFxuICAgICAgICBfb25FeGl0ZWQgPSBfdGhpcyRwcm9wcy5vbkV4aXRlZCxcbiAgICAgICAgX25vZGVSZWYgPSBfdGhpcyRwcm9wcy5ub2RlUmVmLFxuICAgICAgICBjaGlsZFByb3BzID0gX29iamVjdFdpdGhvdXRQcm9wZXJ0aWVzTG9vc2UoX3RoaXMkcHJvcHMsIFtcImNoaWxkcmVuXCIsIFwiaW5cIiwgXCJtb3VudE9uRW50ZXJcIiwgXCJ1bm1vdW50T25FeGl0XCIsIFwiYXBwZWFyXCIsIFwiZW50ZXJcIiwgXCJleGl0XCIsIFwidGltZW91dFwiLCBcImFkZEVuZExpc3RlbmVyXCIsIFwib25FbnRlclwiLCBcIm9uRW50ZXJpbmdcIiwgXCJvbkVudGVyZWRcIiwgXCJvbkV4aXRcIiwgXCJvbkV4aXRpbmdcIiwgXCJvbkV4aXRlZFwiLCBcIm5vZGVSZWZcIl0pO1xuXG4gICAgcmV0dXJuIChcbiAgICAgIC8qI19fUFVSRV9fKi9cbiAgICAgIC8vIGFsbG93cyBmb3IgbmVzdGVkIFRyYW5zaXRpb25zXG4gICAgICBSZWFjdC5jcmVhdGVFbGVtZW50KFRyYW5zaXRpb25Hcm91cENvbnRleHQuUHJvdmlkZXIsIHtcbiAgICAgICAgdmFsdWU6IG51bGxcbiAgICAgIH0sIHR5cGVvZiBjaGlsZHJlbiA9PT0gJ2Z1bmN0aW9uJyA/IGNoaWxkcmVuKHN0YXR1cywgY2hpbGRQcm9wcykgOiBSZWFjdC5jbG9uZUVsZW1lbnQoUmVhY3QuQ2hpbGRyZW4ub25seShjaGlsZHJlbiksIGNoaWxkUHJvcHMpKVxuICAgICk7XG4gIH07XG5cbiAgcmV0dXJuIFRyYW5zaXRpb247XG59KFJlYWN0LkNvbXBvbmVudCk7XG5cblRyYW5zaXRpb24uY29udGV4dFR5cGUgPSBUcmFuc2l0aW9uR3JvdXBDb250ZXh0O1xuVHJhbnNpdGlvbi5wcm9wVHlwZXMgPSBwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gXCJwcm9kdWN0aW9uXCIgPyB7XG4gIC8qKlxuICAgKiBBIFJlYWN0IHJlZmVyZW5jZSB0byBET00gZWxlbWVudCB0aGF0IG5lZWQgdG8gdHJhbnNpdGlvbjpcbiAgICogaHR0cHM6Ly9zdGFja292ZXJmbG93LmNvbS9hLzUxMTI3MTMwLzQ2NzE5MzJcbiAgICpcbiAgICogICAtIFdoZW4gYG5vZGVSZWZgIHByb3AgaXMgdXNlZCwgYG5vZGVgIGlzIG5vdCBwYXNzZWQgdG8gY2FsbGJhY2sgZnVuY3Rpb25zXG4gICAqICAgICAgKGUuZy4gYG9uRW50ZXJgKSBiZWNhdXNlIHVzZXIgYWxyZWFkeSBoYXMgZGlyZWN0IGFjY2VzcyB0byB0aGUgbm9kZS5cbiAgICogICAtIFdoZW4gY2hhbmdpbmcgYGtleWAgcHJvcCBvZiBgVHJhbnNpdGlvbmAgaW4gYSBgVHJhbnNpdGlvbkdyb3VwYCBhIG5ld1xuICAgKiAgICAgYG5vZGVSZWZgIG5lZWQgdG8gYmUgcHJvdmlkZWQgdG8gYFRyYW5zaXRpb25gIHdpdGggY2hhbmdlZCBga2V5YCBwcm9wXG4gICAqICAgICAoc2VlXG4gICAqICAgICBbdGVzdC9DU1NUcmFuc2l0aW9uLXRlc3QuanNdKGh0dHBzOi8vZ2l0aHViLmNvbS9yZWFjdGpzL3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvYmxvYi8xMzQzNWY4OTdiM2FiNzFmNmUxOWQ3MjRmMTQ1NTk2ZjU5MTA1ODFjL3Rlc3QvQ1NTVHJhbnNpdGlvbi10ZXN0LmpzI0wzNjItTDQzNykpLlxuICAgKi9cbiAgbm9kZVJlZjogUHJvcFR5cGVzLnNoYXBlKHtcbiAgICBjdXJyZW50OiB0eXBlb2YgRWxlbWVudCA9PT0gJ3VuZGVmaW5lZCcgPyBQcm9wVHlwZXMuYW55IDogZnVuY3Rpb24gKHByb3BWYWx1ZSwga2V5LCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lLCBzZWNyZXQpIHtcbiAgICAgIHZhciB2YWx1ZSA9IHByb3BWYWx1ZVtrZXldO1xuICAgICAgcmV0dXJuIFByb3BUeXBlcy5pbnN0YW5jZU9mKHZhbHVlICYmICdvd25lckRvY3VtZW50JyBpbiB2YWx1ZSA/IHZhbHVlLm93bmVyRG9jdW1lbnQuZGVmYXVsdFZpZXcuRWxlbWVudCA6IEVsZW1lbnQpKHByb3BWYWx1ZSwga2V5LCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lLCBzZWNyZXQpO1xuICAgIH1cbiAgfSksXG5cbiAgLyoqXG4gICAqIEEgYGZ1bmN0aW9uYCBjaGlsZCBjYW4gYmUgdXNlZCBpbnN0ZWFkIG9mIGEgUmVhY3QgZWxlbWVudC4gVGhpcyBmdW5jdGlvbiBpc1xuICAgKiBjYWxsZWQgd2l0aCB0aGUgY3VycmVudCB0cmFuc2l0aW9uIHN0YXR1cyAoYCdlbnRlcmluZydgLCBgJ2VudGVyZWQnYCxcbiAgICogYCdleGl0aW5nJ2AsIGAnZXhpdGVkJ2ApLCB3aGljaCBjYW4gYmUgdXNlZCB0byBhcHBseSBjb250ZXh0XG4gICAqIHNwZWNpZmljIHByb3BzIHRvIGEgY29tcG9uZW50LlxuICAgKlxuICAgKiBgYGBqc3hcbiAgICogPFRyYW5zaXRpb24gaW49e3RoaXMuc3RhdGUuaW59IHRpbWVvdXQ9ezE1MH0+XG4gICAqICAge3N0YXRlID0+IChcbiAgICogICAgIDxNeUNvbXBvbmVudCBjbGFzc05hbWU9e2BmYWRlIGZhZGUtJHtzdGF0ZX1gfSAvPlxuICAgKiAgICl9XG4gICAqIDwvVHJhbnNpdGlvbj5cbiAgICogYGBgXG4gICAqL1xuICBjaGlsZHJlbjogUHJvcFR5cGVzLm9uZU9mVHlwZShbUHJvcFR5cGVzLmZ1bmMuaXNSZXF1aXJlZCwgUHJvcFR5cGVzLmVsZW1lbnQuaXNSZXF1aXJlZF0pLmlzUmVxdWlyZWQsXG5cbiAgLyoqXG4gICAqIFNob3cgdGhlIGNvbXBvbmVudDsgdHJpZ2dlcnMgdGhlIGVudGVyIG9yIGV4aXQgc3RhdGVzXG4gICAqL1xuICBpbjogUHJvcFR5cGVzLmJvb2wsXG5cbiAgLyoqXG4gICAqIEJ5IGRlZmF1bHQgdGhlIGNoaWxkIGNvbXBvbmVudCBpcyBtb3VudGVkIGltbWVkaWF0ZWx5IGFsb25nIHdpdGhcbiAgICogdGhlIHBhcmVudCBgVHJhbnNpdGlvbmAgY29tcG9uZW50LiBJZiB5b3Ugd2FudCB0byBcImxhenkgbW91bnRcIiB0aGUgY29tcG9uZW50IG9uIHRoZVxuICAgKiBmaXJzdCBgaW49e3RydWV9YCB5b3UgY2FuIHNldCBgbW91bnRPbkVudGVyYC4gQWZ0ZXIgdGhlIGZpcnN0IGVudGVyIHRyYW5zaXRpb24gdGhlIGNvbXBvbmVudCB3aWxsIHN0YXlcbiAgICogbW91bnRlZCwgZXZlbiBvbiBcImV4aXRlZFwiLCB1bmxlc3MgeW91IGFsc28gc3BlY2lmeSBgdW5tb3VudE9uRXhpdGAuXG4gICAqL1xuICBtb3VudE9uRW50ZXI6IFByb3BUeXBlcy5ib29sLFxuXG4gIC8qKlxuICAgKiBCeSBkZWZhdWx0IHRoZSBjaGlsZCBjb21wb25lbnQgc3RheXMgbW91bnRlZCBhZnRlciBpdCByZWFjaGVzIHRoZSBgJ2V4aXRlZCdgIHN0YXRlLlxuICAgKiBTZXQgYHVubW91bnRPbkV4aXRgIGlmIHlvdSdkIHByZWZlciB0byB1bm1vdW50IHRoZSBjb21wb25lbnQgYWZ0ZXIgaXQgZmluaXNoZXMgZXhpdGluZy5cbiAgICovXG4gIHVubW91bnRPbkV4aXQ6IFByb3BUeXBlcy5ib29sLFxuXG4gIC8qKlxuICAgKiBCeSBkZWZhdWx0IHRoZSBjaGlsZCBjb21wb25lbnQgZG9lcyBub3QgcGVyZm9ybSB0aGUgZW50ZXIgdHJhbnNpdGlvbiB3aGVuXG4gICAqIGl0IGZpcnN0IG1vdW50cywgcmVnYXJkbGVzcyBvZiB0aGUgdmFsdWUgb2YgYGluYC4gSWYgeW91IHdhbnQgdGhpc1xuICAgKiBiZWhhdmlvciwgc2V0IGJvdGggYGFwcGVhcmAgYW5kIGBpbmAgdG8gYHRydWVgLlxuICAgKlxuICAgKiA+ICoqTm90ZSoqOiB0aGVyZSBhcmUgbm8gc3BlY2lhbCBhcHBlYXIgc3RhdGVzIGxpa2UgYGFwcGVhcmluZ2AvYGFwcGVhcmVkYCwgdGhpcyBwcm9wXG4gICAqID4gb25seSBhZGRzIGFuIGFkZGl0aW9uYWwgZW50ZXIgdHJhbnNpdGlvbi4gSG93ZXZlciwgaW4gdGhlXG4gICAqID4gYDxDU1NUcmFuc2l0aW9uPmAgY29tcG9uZW50IHRoYXQgZmlyc3QgZW50ZXIgdHJhbnNpdGlvbiBkb2VzIHJlc3VsdCBpblxuICAgKiA+IGFkZGl0aW9uYWwgYC5hcHBlYXItKmAgY2xhc3NlcywgdGhhdCB3YXkgeW91IGNhbiBjaG9vc2UgdG8gc3R5bGUgaXRcbiAgICogPiBkaWZmZXJlbnRseS5cbiAgICovXG4gIGFwcGVhcjogUHJvcFR5cGVzLmJvb2wsXG5cbiAgLyoqXG4gICAqIEVuYWJsZSBvciBkaXNhYmxlIGVudGVyIHRyYW5zaXRpb25zLlxuICAgKi9cbiAgZW50ZXI6IFByb3BUeXBlcy5ib29sLFxuXG4gIC8qKlxuICAgKiBFbmFibGUgb3IgZGlzYWJsZSBleGl0IHRyYW5zaXRpb25zLlxuICAgKi9cbiAgZXhpdDogUHJvcFR5cGVzLmJvb2wsXG5cbiAgLyoqXG4gICAqIFRoZSBkdXJhdGlvbiBvZiB0aGUgdHJhbnNpdGlvbiwgaW4gbWlsbGlzZWNvbmRzLlxuICAgKiBSZXF1aXJlZCB1bmxlc3MgYGFkZEVuZExpc3RlbmVyYCBpcyBwcm92aWRlZC5cbiAgICpcbiAgICogWW91IG1heSBzcGVjaWZ5IGEgc2luZ2xlIHRpbWVvdXQgZm9yIGFsbCB0cmFuc2l0aW9uczpcbiAgICpcbiAgICogYGBganN4XG4gICAqIHRpbWVvdXQ9ezUwMH1cbiAgICogYGBgXG4gICAqXG4gICAqIG9yIGluZGl2aWR1YWxseTpcbiAgICpcbiAgICogYGBganN4XG4gICAqIHRpbWVvdXQ9e3tcbiAgICogIGFwcGVhcjogNTAwLFxuICAgKiAgZW50ZXI6IDMwMCxcbiAgICogIGV4aXQ6IDUwMCxcbiAgICogfX1cbiAgICogYGBgXG4gICAqXG4gICAqIC0gYGFwcGVhcmAgZGVmYXVsdHMgdG8gdGhlIHZhbHVlIG9mIGBlbnRlcmBcbiAgICogLSBgZW50ZXJgIGRlZmF1bHRzIHRvIGAwYFxuICAgKiAtIGBleGl0YCBkZWZhdWx0cyB0byBgMGBcbiAgICpcbiAgICogQHR5cGUge251bWJlciB8IHsgZW50ZXI/OiBudW1iZXIsIGV4aXQ/OiBudW1iZXIsIGFwcGVhcj86IG51bWJlciB9fVxuICAgKi9cbiAgdGltZW91dDogZnVuY3Rpb24gdGltZW91dChwcm9wcykge1xuICAgIHZhciBwdCA9IHRpbWVvdXRzU2hhcGU7XG4gICAgaWYgKCFwcm9wcy5hZGRFbmRMaXN0ZW5lcikgcHQgPSBwdC5pc1JlcXVpcmVkO1xuXG4gICAgZm9yICh2YXIgX2xlbiA9IGFyZ3VtZW50cy5sZW5ndGgsIGFyZ3MgPSBuZXcgQXJyYXkoX2xlbiA+IDEgPyBfbGVuIC0gMSA6IDApLCBfa2V5ID0gMTsgX2tleSA8IF9sZW47IF9rZXkrKykge1xuICAgICAgYXJnc1tfa2V5IC0gMV0gPSBhcmd1bWVudHNbX2tleV07XG4gICAgfVxuXG4gICAgcmV0dXJuIHB0LmFwcGx5KHZvaWQgMCwgW3Byb3BzXS5jb25jYXQoYXJncykpO1xuICB9LFxuXG4gIC8qKlxuICAgKiBBZGQgYSBjdXN0b20gdHJhbnNpdGlvbiBlbmQgdHJpZ2dlci4gQ2FsbGVkIHdpdGggdGhlIHRyYW5zaXRpb25pbmdcbiAgICogRE9NIG5vZGUgYW5kIGEgYGRvbmVgIGNhbGxiYWNrLiBBbGxvd3MgZm9yIG1vcmUgZmluZSBncmFpbmVkIHRyYW5zaXRpb24gZW5kXG4gICAqIGxvZ2ljLiBUaW1lb3V0cyBhcmUgc3RpbGwgdXNlZCBhcyBhIGZhbGxiYWNrIGlmIHByb3ZpZGVkLlxuICAgKlxuICAgKiAqKk5vdGUqKjogd2hlbiBgbm9kZVJlZmAgcHJvcCBpcyBwYXNzZWQsIGBub2RlYCBpcyBub3QgcGFzc2VkLlxuICAgKlxuICAgKiBgYGBqc3hcbiAgICogYWRkRW5kTGlzdGVuZXI9eyhub2RlLCBkb25lKSA9PiB7XG4gICAqICAgLy8gdXNlIHRoZSBjc3MgdHJhbnNpdGlvbmVuZCBldmVudCB0byBtYXJrIHRoZSBmaW5pc2ggb2YgYSB0cmFuc2l0aW9uXG4gICAqICAgbm9kZS5hZGRFdmVudExpc3RlbmVyKCd0cmFuc2l0aW9uZW5kJywgZG9uZSwgZmFsc2UpO1xuICAgKiB9fVxuICAgKiBgYGBcbiAgICovXG4gIGFkZEVuZExpc3RlbmVyOiBQcm9wVHlwZXMuZnVuYyxcblxuICAvKipcbiAgICogQ2FsbGJhY2sgZmlyZWQgYmVmb3JlIHRoZSBcImVudGVyaW5nXCIgc3RhdHVzIGlzIGFwcGxpZWQuIEFuIGV4dHJhIHBhcmFtZXRlclxuICAgKiBgaXNBcHBlYXJpbmdgIGlzIHN1cHBsaWVkIHRvIGluZGljYXRlIGlmIHRoZSBlbnRlciBzdGFnZSBpcyBvY2N1cnJpbmcgb24gdGhlIGluaXRpYWwgbW91bnRcbiAgICpcbiAgICogKipOb3RlKio6IHdoZW4gYG5vZGVSZWZgIHByb3AgaXMgcGFzc2VkLCBgbm9kZWAgaXMgbm90IHBhc3NlZC5cbiAgICpcbiAgICogQHR5cGUgRnVuY3Rpb24obm9kZTogSHRtbEVsZW1lbnQsIGlzQXBwZWFyaW5nOiBib29sKSAtPiB2b2lkXG4gICAqL1xuICBvbkVudGVyOiBQcm9wVHlwZXMuZnVuYyxcblxuICAvKipcbiAgICogQ2FsbGJhY2sgZmlyZWQgYWZ0ZXIgdGhlIFwiZW50ZXJpbmdcIiBzdGF0dXMgaXMgYXBwbGllZC4gQW4gZXh0cmEgcGFyYW1ldGVyXG4gICAqIGBpc0FwcGVhcmluZ2AgaXMgc3VwcGxpZWQgdG8gaW5kaWNhdGUgaWYgdGhlIGVudGVyIHN0YWdlIGlzIG9jY3VycmluZyBvbiB0aGUgaW5pdGlhbCBtb3VudFxuICAgKlxuICAgKiAqKk5vdGUqKjogd2hlbiBgbm9kZVJlZmAgcHJvcCBpcyBwYXNzZWQsIGBub2RlYCBpcyBub3QgcGFzc2VkLlxuICAgKlxuICAgKiBAdHlwZSBGdW5jdGlvbihub2RlOiBIdG1sRWxlbWVudCwgaXNBcHBlYXJpbmc6IGJvb2wpXG4gICAqL1xuICBvbkVudGVyaW5nOiBQcm9wVHlwZXMuZnVuYyxcblxuICAvKipcbiAgICogQ2FsbGJhY2sgZmlyZWQgYWZ0ZXIgdGhlIFwiZW50ZXJlZFwiIHN0YXR1cyBpcyBhcHBsaWVkLiBBbiBleHRyYSBwYXJhbWV0ZXJcbiAgICogYGlzQXBwZWFyaW5nYCBpcyBzdXBwbGllZCB0byBpbmRpY2F0ZSBpZiB0aGUgZW50ZXIgc3RhZ2UgaXMgb2NjdXJyaW5nIG9uIHRoZSBpbml0aWFsIG1vdW50XG4gICAqXG4gICAqICoqTm90ZSoqOiB3aGVuIGBub2RlUmVmYCBwcm9wIGlzIHBhc3NlZCwgYG5vZGVgIGlzIG5vdCBwYXNzZWQuXG4gICAqXG4gICAqIEB0eXBlIEZ1bmN0aW9uKG5vZGU6IEh0bWxFbGVtZW50LCBpc0FwcGVhcmluZzogYm9vbCkgLT4gdm9pZFxuICAgKi9cbiAgb25FbnRlcmVkOiBQcm9wVHlwZXMuZnVuYyxcblxuICAvKipcbiAgICogQ2FsbGJhY2sgZmlyZWQgYmVmb3JlIHRoZSBcImV4aXRpbmdcIiBzdGF0dXMgaXMgYXBwbGllZC5cbiAgICpcbiAgICogKipOb3RlKio6IHdoZW4gYG5vZGVSZWZgIHByb3AgaXMgcGFzc2VkLCBgbm9kZWAgaXMgbm90IHBhc3NlZC5cbiAgICpcbiAgICogQHR5cGUgRnVuY3Rpb24obm9kZTogSHRtbEVsZW1lbnQpIC0+IHZvaWRcbiAgICovXG4gIG9uRXhpdDogUHJvcFR5cGVzLmZ1bmMsXG5cbiAgLyoqXG4gICAqIENhbGxiYWNrIGZpcmVkIGFmdGVyIHRoZSBcImV4aXRpbmdcIiBzdGF0dXMgaXMgYXBwbGllZC5cbiAgICpcbiAgICogKipOb3RlKio6IHdoZW4gYG5vZGVSZWZgIHByb3AgaXMgcGFzc2VkLCBgbm9kZWAgaXMgbm90IHBhc3NlZC5cbiAgICpcbiAgICogQHR5cGUgRnVuY3Rpb24obm9kZTogSHRtbEVsZW1lbnQpIC0+IHZvaWRcbiAgICovXG4gIG9uRXhpdGluZzogUHJvcFR5cGVzLmZ1bmMsXG5cbiAgLyoqXG4gICAqIENhbGxiYWNrIGZpcmVkIGFmdGVyIHRoZSBcImV4aXRlZFwiIHN0YXR1cyBpcyBhcHBsaWVkLlxuICAgKlxuICAgKiAqKk5vdGUqKjogd2hlbiBgbm9kZVJlZmAgcHJvcCBpcyBwYXNzZWQsIGBub2RlYCBpcyBub3QgcGFzc2VkXG4gICAqXG4gICAqIEB0eXBlIEZ1bmN0aW9uKG5vZGU6IEh0bWxFbGVtZW50KSAtPiB2b2lkXG4gICAqL1xuICBvbkV4aXRlZDogUHJvcFR5cGVzLmZ1bmNcbn0gOiB7fTsgLy8gTmFtZSB0aGUgZnVuY3Rpb24gc28gaXQgaXMgY2xlYXJlciBpbiB0aGUgZG9jdW1lbnRhdGlvblxuXG5mdW5jdGlvbiBub29wKCkge31cblxuVHJhbnNpdGlvbi5kZWZhdWx0UHJvcHMgPSB7XG4gIGluOiBmYWxzZSxcbiAgbW91bnRPbkVudGVyOiBmYWxzZSxcbiAgdW5tb3VudE9uRXhpdDogZmFsc2UsXG4gIGFwcGVhcjogZmFsc2UsXG4gIGVudGVyOiB0cnVlLFxuICBleGl0OiB0cnVlLFxuICBvbkVudGVyOiBub29wLFxuICBvbkVudGVyaW5nOiBub29wLFxuICBvbkVudGVyZWQ6IG5vb3AsXG4gIG9uRXhpdDogbm9vcCxcbiAgb25FeGl0aW5nOiBub29wLFxuICBvbkV4aXRlZDogbm9vcFxufTtcblRyYW5zaXRpb24uVU5NT1VOVEVEID0gVU5NT1VOVEVEO1xuVHJhbnNpdGlvbi5FWElURUQgPSBFWElURUQ7XG5UcmFuc2l0aW9uLkVOVEVSSU5HID0gRU5URVJJTkc7XG5UcmFuc2l0aW9uLkVOVEVSRUQgPSBFTlRFUkVEO1xuVHJhbnNpdGlvbi5FWElUSU5HID0gRVhJVElORztcbmV4cG9ydCBkZWZhdWx0IFRyYW5zaXRpb247IiwiZXhwb3J0IGRlZmF1bHQgISEodHlwZW9mIHdpbmRvdyAhPT0gJ3VuZGVmaW5lZCcgJiYgd2luZG93LmRvY3VtZW50ICYmIHdpbmRvdy5kb2N1bWVudC5jcmVhdGVFbGVtZW50KTsiLCIvKiBlc2xpbnQtZGlzYWJsZSBuby1yZXR1cm4tYXNzaWduICovXG5pbXBvcnQgY2FuVXNlRE9NIGZyb20gJy4vY2FuVXNlRE9NJztcbmV4cG9ydCB2YXIgb3B0aW9uc1N1cHBvcnRlZCA9IGZhbHNlO1xuZXhwb3J0IHZhciBvbmNlU3VwcG9ydGVkID0gZmFsc2U7XG5cbnRyeSB7XG4gIHZhciBvcHRpb25zID0ge1xuICAgIGdldCBwYXNzaXZlKCkge1xuICAgICAgcmV0dXJuIG9wdGlvbnNTdXBwb3J0ZWQgPSB0cnVlO1xuICAgIH0sXG5cbiAgICBnZXQgb25jZSgpIHtcbiAgICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBuby1tdWx0aS1hc3NpZ25cbiAgICAgIHJldHVybiBvbmNlU3VwcG9ydGVkID0gb3B0aW9uc1N1cHBvcnRlZCA9IHRydWU7XG4gICAgfVxuXG4gIH07XG5cbiAgaWYgKGNhblVzZURPTSkge1xuICAgIHdpbmRvdy5hZGRFdmVudExpc3RlbmVyKCd0ZXN0Jywgb3B0aW9ucywgb3B0aW9ucyk7XG4gICAgd2luZG93LnJlbW92ZUV2ZW50TGlzdGVuZXIoJ3Rlc3QnLCBvcHRpb25zLCB0cnVlKTtcbiAgfVxufSBjYXRjaCAoZSkge1xuICAvKiAqL1xufVxuXG4vKipcbiAqIEFuIGBhZGRFdmVudExpc3RlbmVyYCBwb255ZmlsbCwgc3VwcG9ydHMgdGhlIGBvbmNlYCBvcHRpb25cbiAqIFxuICogQHBhcmFtIG5vZGUgdGhlIGVsZW1lbnRcbiAqIEBwYXJhbSBldmVudE5hbWUgdGhlIGV2ZW50IG5hbWVcbiAqIEBwYXJhbSBoYW5kbGUgdGhlIGhhbmRsZXJcbiAqIEBwYXJhbSBvcHRpb25zIGV2ZW50IG9wdGlvbnNcbiAqL1xuZnVuY3Rpb24gYWRkRXZlbnRMaXN0ZW5lcihub2RlLCBldmVudE5hbWUsIGhhbmRsZXIsIG9wdGlvbnMpIHtcbiAgaWYgKG9wdGlvbnMgJiYgdHlwZW9mIG9wdGlvbnMgIT09ICdib29sZWFuJyAmJiAhb25jZVN1cHBvcnRlZCkge1xuICAgIHZhciBvbmNlID0gb3B0aW9ucy5vbmNlLFxuICAgICAgICBjYXB0dXJlID0gb3B0aW9ucy5jYXB0dXJlO1xuICAgIHZhciB3cmFwcGVkSGFuZGxlciA9IGhhbmRsZXI7XG5cbiAgICBpZiAoIW9uY2VTdXBwb3J0ZWQgJiYgb25jZSkge1xuICAgICAgd3JhcHBlZEhhbmRsZXIgPSBoYW5kbGVyLl9fb25jZSB8fCBmdW5jdGlvbiBvbmNlSGFuZGxlcihldmVudCkge1xuICAgICAgICB0aGlzLnJlbW92ZUV2ZW50TGlzdGVuZXIoZXZlbnROYW1lLCBvbmNlSGFuZGxlciwgY2FwdHVyZSk7XG4gICAgICAgIGhhbmRsZXIuY2FsbCh0aGlzLCBldmVudCk7XG4gICAgICB9O1xuXG4gICAgICBoYW5kbGVyLl9fb25jZSA9IHdyYXBwZWRIYW5kbGVyO1xuICAgIH1cblxuICAgIG5vZGUuYWRkRXZlbnRMaXN0ZW5lcihldmVudE5hbWUsIHdyYXBwZWRIYW5kbGVyLCBvcHRpb25zU3VwcG9ydGVkID8gb3B0aW9ucyA6IGNhcHR1cmUpO1xuICB9XG5cbiAgbm9kZS5hZGRFdmVudExpc3RlbmVyKGV2ZW50TmFtZSwgaGFuZGxlciwgb3B0aW9ucyk7XG59XG5cbmV4cG9ydCBkZWZhdWx0IGFkZEV2ZW50TGlzdGVuZXI7IiwiLyoqXG4gKiBBIGByZW1vdmVFdmVudExpc3RlbmVyYCBwb255ZmlsbFxuICogXG4gKiBAcGFyYW0gbm9kZSB0aGUgZWxlbWVudFxuICogQHBhcmFtIGV2ZW50TmFtZSB0aGUgZXZlbnQgbmFtZVxuICogQHBhcmFtIGhhbmRsZSB0aGUgaGFuZGxlclxuICogQHBhcmFtIG9wdGlvbnMgZXZlbnQgb3B0aW9uc1xuICovXG5mdW5jdGlvbiByZW1vdmVFdmVudExpc3RlbmVyKG5vZGUsIGV2ZW50TmFtZSwgaGFuZGxlciwgb3B0aW9ucykge1xuICB2YXIgY2FwdHVyZSA9IG9wdGlvbnMgJiYgdHlwZW9mIG9wdGlvbnMgIT09ICdib29sZWFuJyA/IG9wdGlvbnMuY2FwdHVyZSA6IG9wdGlvbnM7XG4gIG5vZGUucmVtb3ZlRXZlbnRMaXN0ZW5lcihldmVudE5hbWUsIGhhbmRsZXIsIGNhcHR1cmUpO1xuXG4gIGlmIChoYW5kbGVyLl9fb25jZSkge1xuICAgIG5vZGUucmVtb3ZlRXZlbnRMaXN0ZW5lcihldmVudE5hbWUsIGhhbmRsZXIuX19vbmNlLCBjYXB0dXJlKTtcbiAgfVxufVxuXG5leHBvcnQgZGVmYXVsdCByZW1vdmVFdmVudExpc3RlbmVyOyIsImltcG9ydCBhZGRFdmVudExpc3RlbmVyIGZyb20gJy4vYWRkRXZlbnRMaXN0ZW5lcic7XG5pbXBvcnQgcmVtb3ZlRXZlbnRMaXN0ZW5lciBmcm9tICcuL3JlbW92ZUV2ZW50TGlzdGVuZXInO1xuXG5mdW5jdGlvbiBsaXN0ZW4obm9kZSwgZXZlbnROYW1lLCBoYW5kbGVyLCBvcHRpb25zKSB7XG4gIGFkZEV2ZW50TGlzdGVuZXIobm9kZSwgZXZlbnROYW1lLCBoYW5kbGVyLCBvcHRpb25zKTtcbiAgcmV0dXJuIGZ1bmN0aW9uICgpIHtcbiAgICByZW1vdmVFdmVudExpc3RlbmVyKG5vZGUsIGV2ZW50TmFtZSwgaGFuZGxlciwgb3B0aW9ucyk7XG4gIH07XG59XG5cbmV4cG9ydCBkZWZhdWx0IGxpc3RlbjsiLCIvKipcbiAqIFRyaWdnZXJzIGFuIGV2ZW50IG9uIGEgZ2l2ZW4gZWxlbWVudC5cbiAqIFxuICogQHBhcmFtIG5vZGUgdGhlIGVsZW1lbnRcbiAqIEBwYXJhbSBldmVudE5hbWUgdGhlIGV2ZW50IG5hbWUgdG8gdHJpZ2dlclxuICogQHBhcmFtIGJ1YmJsZXMgd2hldGhlciB0aGUgZXZlbnQgc2hvdWxkIGJ1YmJsZSB1cFxuICogQHBhcmFtIGNhbmNlbGFibGUgd2hldGhlciB0aGUgZXZlbnQgc2hvdWxkIGJlIGNhbmNlbGFibGVcbiAqL1xuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gdHJpZ2dlckV2ZW50KG5vZGUsIGV2ZW50TmFtZSwgYnViYmxlcywgY2FuY2VsYWJsZSkge1xuICBpZiAoYnViYmxlcyA9PT0gdm9pZCAwKSB7XG4gICAgYnViYmxlcyA9IGZhbHNlO1xuICB9XG5cbiAgaWYgKGNhbmNlbGFibGUgPT09IHZvaWQgMCkge1xuICAgIGNhbmNlbGFibGUgPSB0cnVlO1xuICB9XG5cbiAgaWYgKG5vZGUpIHtcbiAgICB2YXIgZXZlbnQgPSBkb2N1bWVudC5jcmVhdGVFdmVudCgnSFRNTEV2ZW50cycpO1xuICAgIGV2ZW50LmluaXRFdmVudChldmVudE5hbWUsIGJ1YmJsZXMsIGNhbmNlbGFibGUpO1xuICAgIG5vZGUuZGlzcGF0Y2hFdmVudChldmVudCk7XG4gIH1cbn0iLCJpbXBvcnQgY3NzIGZyb20gJy4vY3NzJztcbmltcG9ydCBsaXN0ZW4gZnJvbSAnLi9saXN0ZW4nO1xuaW1wb3J0IHRyaWdnZXJFdmVudCBmcm9tICcuL3RyaWdnZXJFdmVudCc7XG5cbmZ1bmN0aW9uIHBhcnNlRHVyYXRpb24obm9kZSkge1xuICB2YXIgc3RyID0gY3NzKG5vZGUsICd0cmFuc2l0aW9uRHVyYXRpb24nKSB8fCAnJztcbiAgdmFyIG11bHQgPSBzdHIuaW5kZXhPZignbXMnKSA9PT0gLTEgPyAxMDAwIDogMTtcbiAgcmV0dXJuIHBhcnNlRmxvYXQoc3RyKSAqIG11bHQ7XG59XG5cbmZ1bmN0aW9uIGVtdWxhdGVUcmFuc2l0aW9uRW5kKGVsZW1lbnQsIGR1cmF0aW9uLCBwYWRkaW5nKSB7XG4gIGlmIChwYWRkaW5nID09PSB2b2lkIDApIHtcbiAgICBwYWRkaW5nID0gNTtcbiAgfVxuXG4gIHZhciBjYWxsZWQgPSBmYWxzZTtcbiAgdmFyIGhhbmRsZSA9IHNldFRpbWVvdXQoZnVuY3Rpb24gKCkge1xuICAgIGlmICghY2FsbGVkKSB0cmlnZ2VyRXZlbnQoZWxlbWVudCwgJ3RyYW5zaXRpb25lbmQnLCB0cnVlKTtcbiAgfSwgZHVyYXRpb24gKyBwYWRkaW5nKTtcbiAgdmFyIHJlbW92ZSA9IGxpc3RlbihlbGVtZW50LCAndHJhbnNpdGlvbmVuZCcsIGZ1bmN0aW9uICgpIHtcbiAgICBjYWxsZWQgPSB0cnVlO1xuICB9LCB7XG4gICAgb25jZTogdHJ1ZVxuICB9KTtcbiAgcmV0dXJuIGZ1bmN0aW9uICgpIHtcbiAgICBjbGVhclRpbWVvdXQoaGFuZGxlKTtcbiAgICByZW1vdmUoKTtcbiAgfTtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gdHJhbnNpdGlvbkVuZChlbGVtZW50LCBoYW5kbGVyLCBkdXJhdGlvbiwgcGFkZGluZykge1xuICBpZiAoZHVyYXRpb24gPT0gbnVsbCkgZHVyYXRpb24gPSBwYXJzZUR1cmF0aW9uKGVsZW1lbnQpIHx8IDA7XG4gIHZhciByZW1vdmVFbXVsYXRlID0gZW11bGF0ZVRyYW5zaXRpb25FbmQoZWxlbWVudCwgZHVyYXRpb24sIHBhZGRpbmcpO1xuICB2YXIgcmVtb3ZlID0gbGlzdGVuKGVsZW1lbnQsICd0cmFuc2l0aW9uZW5kJywgaGFuZGxlcik7XG4gIHJldHVybiBmdW5jdGlvbiAoKSB7XG4gICAgcmVtb3ZlRW11bGF0ZSgpO1xuICAgIHJlbW92ZSgpO1xuICB9O1xufSIsImltcG9ydCBjc3MgZnJvbSAnZG9tLWhlbHBlcnMvY3NzJztcbmltcG9ydCB0cmFuc2l0aW9uRW5kIGZyb20gJ2RvbS1oZWxwZXJzL3RyYW5zaXRpb25FbmQnO1xuZnVuY3Rpb24gcGFyc2VEdXJhdGlvbihub2RlLCBwcm9wZXJ0eSkge1xuICBjb25zdCBzdHIgPSBjc3Mobm9kZSwgcHJvcGVydHkpIHx8ICcnO1xuICBjb25zdCBtdWx0ID0gc3RyLmluZGV4T2YoJ21zJykgPT09IC0xID8gMTAwMCA6IDE7XG4gIHJldHVybiBwYXJzZUZsb2F0KHN0cikgKiBtdWx0O1xufVxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gdHJhbnNpdGlvbkVuZExpc3RlbmVyKGVsZW1lbnQsIGhhbmRsZXIpIHtcbiAgY29uc3QgZHVyYXRpb24gPSBwYXJzZUR1cmF0aW9uKGVsZW1lbnQsICd0cmFuc2l0aW9uRHVyYXRpb24nKTtcbiAgY29uc3QgZGVsYXkgPSBwYXJzZUR1cmF0aW9uKGVsZW1lbnQsICd0cmFuc2l0aW9uRGVsYXknKTtcbiAgY29uc3QgcmVtb3ZlID0gdHJhbnNpdGlvbkVuZChlbGVtZW50LCBlID0+IHtcbiAgICBpZiAoZS50YXJnZXQgPT09IGVsZW1lbnQpIHtcbiAgICAgIHJlbW92ZSgpO1xuICAgICAgaGFuZGxlcihlKTtcbiAgICB9XG4gIH0sIGR1cmF0aW9uICsgZGVsYXkpO1xufSIsIi8qKlxuICogU2FmZSBjaGFpbmVkIGZ1bmN0aW9uXG4gKlxuICogV2lsbCBvbmx5IGNyZWF0ZSBhIG5ldyBmdW5jdGlvbiBpZiBuZWVkZWQsXG4gKiBvdGhlcndpc2Ugd2lsbCBwYXNzIGJhY2sgZXhpc3RpbmcgZnVuY3Rpb25zIG9yIG51bGwuXG4gKlxuICogQHBhcmFtIHtmdW5jdGlvbn0gZnVuY3Rpb25zIHRvIGNoYWluXG4gKiBAcmV0dXJucyB7ZnVuY3Rpb258bnVsbH1cbiAqL1xuZnVuY3Rpb24gY3JlYXRlQ2hhaW5lZEZ1bmN0aW9uKC4uLmZ1bmNzKSB7XG4gIHJldHVybiBmdW5jcy5maWx0ZXIoZiA9PiBmICE9IG51bGwpLnJlZHVjZSgoYWNjLCBmKSA9PiB7XG4gICAgaWYgKHR5cGVvZiBmICE9PSAnZnVuY3Rpb24nKSB7XG4gICAgICB0aHJvdyBuZXcgRXJyb3IoJ0ludmFsaWQgQXJndW1lbnQgVHlwZSwgbXVzdCBvbmx5IHByb3ZpZGUgZnVuY3Rpb25zLCB1bmRlZmluZWQsIG9yIG51bGwuJyk7XG4gICAgfVxuICAgIGlmIChhY2MgPT09IG51bGwpIHJldHVybiBmO1xuICAgIHJldHVybiBmdW5jdGlvbiBjaGFpbmVkRnVuY3Rpb24oLi4uYXJncykge1xuICAgICAgLy8gQHRzLWlnbm9yZVxuICAgICAgYWNjLmFwcGx5KHRoaXMsIGFyZ3MpO1xuICAgICAgLy8gQHRzLWlnbm9yZVxuICAgICAgZi5hcHBseSh0aGlzLCBhcmdzKTtcbiAgICB9O1xuICB9LCBudWxsKTtcbn1cbmV4cG9ydCBkZWZhdWx0IGNyZWF0ZUNoYWluZWRGdW5jdGlvbjsiLCIvLyByZWFkaW5nIGEgZGltZW5zaW9uIHByb3Agd2lsbCBjYXVzZSB0aGUgYnJvd3NlciB0byByZWNhbGN1bGF0ZSxcbi8vIHdoaWNoIHdpbGwgbGV0IG91ciBhbmltYXRpb25zIHdvcmtcbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIHRyaWdnZXJCcm93c2VyUmVmbG93KG5vZGUpIHtcbiAgLy8gZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIEB0eXBlc2NyaXB0LWVzbGludC9uby11bnVzZWQtZXhwcmVzc2lvbnNcbiAgbm9kZS5vZmZzZXRIZWlnaHQ7XG59IiwiaW1wb3J0IHsgdXNlTWVtbyB9IGZyb20gJ3JlYWN0JztcblxudmFyIHRvRm5SZWYgPSBmdW5jdGlvbiB0b0ZuUmVmKHJlZikge1xuICByZXR1cm4gIXJlZiB8fCB0eXBlb2YgcmVmID09PSAnZnVuY3Rpb24nID8gcmVmIDogZnVuY3Rpb24gKHZhbHVlKSB7XG4gICAgcmVmLmN1cnJlbnQgPSB2YWx1ZTtcbiAgfTtcbn07XG5cbmV4cG9ydCBmdW5jdGlvbiBtZXJnZVJlZnMocmVmQSwgcmVmQikge1xuICB2YXIgYSA9IHRvRm5SZWYocmVmQSk7XG4gIHZhciBiID0gdG9GblJlZihyZWZCKTtcbiAgcmV0dXJuIGZ1bmN0aW9uICh2YWx1ZSkge1xuICAgIGlmIChhKSBhKHZhbHVlKTtcbiAgICBpZiAoYikgYih2YWx1ZSk7XG4gIH07XG59XG4vKipcbiAqIENyZWF0ZSBhbmQgcmV0dXJucyBhIHNpbmdsZSBjYWxsYmFjayByZWYgY29tcG9zZWQgZnJvbSB0d28gb3RoZXIgUmVmcy5cbiAqXG4gKiBgYGB0c3hcbiAqIGNvbnN0IEJ1dHRvbiA9IFJlYWN0LmZvcndhcmRSZWYoKHByb3BzLCByZWYpID0+IHtcbiAqICAgY29uc3QgW2VsZW1lbnQsIGF0dGFjaFJlZl0gPSB1c2VDYWxsYmFja1JlZjxIVE1MQnV0dG9uRWxlbWVudD4oKTtcbiAqICAgY29uc3QgbWVyZ2VkUmVmID0gdXNlTWVyZ2VkUmVmcyhyZWYsIGF0dGFjaFJlZik7XG4gKlxuICogICByZXR1cm4gPGJ1dHRvbiByZWY9e21lcmdlZFJlZn0gey4uLnByb3BzfS8+XG4gKiB9KVxuICogYGBgXG4gKlxuICogQHBhcmFtIHJlZkEgQSBDYWxsYmFjayBvciBtdXRhYmxlIFJlZlxuICogQHBhcmFtIHJlZkIgQSBDYWxsYmFjayBvciBtdXRhYmxlIFJlZlxuICogQGNhdGVnb3J5IHJlZnNcbiAqL1xuXG5mdW5jdGlvbiB1c2VNZXJnZWRSZWZzKHJlZkEsIHJlZkIpIHtcbiAgcmV0dXJuIHVzZU1lbW8oZnVuY3Rpb24gKCkge1xuICAgIHJldHVybiBtZXJnZVJlZnMocmVmQSwgcmVmQik7XG4gIH0sIFtyZWZBLCByZWZCXSk7XG59XG5cbmV4cG9ydCBkZWZhdWx0IHVzZU1lcmdlZFJlZnM7IiwiaW1wb3J0IFJlYWN0RE9NIGZyb20gJ3JlYWN0LWRvbSc7XG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBzYWZlRmluZERPTU5vZGUoY29tcG9uZW50T3JFbGVtZW50KSB7XG4gIGlmIChjb21wb25lbnRPckVsZW1lbnQgJiYgJ3NldFN0YXRlJyBpbiBjb21wb25lbnRPckVsZW1lbnQpIHtcbiAgICByZXR1cm4gUmVhY3RET00uZmluZERPTU5vZGUoY29tcG9uZW50T3JFbGVtZW50KTtcbiAgfVxuICByZXR1cm4gY29tcG9uZW50T3JFbGVtZW50ICE9IG51bGwgPyBjb21wb25lbnRPckVsZW1lbnQgOiBudWxsO1xufSIsImltcG9ydCBSZWFjdCwgeyB1c2VDYWxsYmFjaywgdXNlUmVmIH0gZnJvbSAncmVhY3QnO1xuaW1wb3J0IFRyYW5zaXRpb24gZnJvbSAncmVhY3QtdHJhbnNpdGlvbi1ncm91cC9UcmFuc2l0aW9uJztcbmltcG9ydCB1c2VNZXJnZWRSZWZzIGZyb20gJ0ByZXN0YXJ0L2hvb2tzL3VzZU1lcmdlZFJlZnMnO1xuaW1wb3J0IHNhZmVGaW5kRE9NTm9kZSBmcm9tICcuL3NhZmVGaW5kRE9NTm9kZSc7XG5pbXBvcnQgeyBqc3ggYXMgX2pzeCB9IGZyb20gXCJyZWFjdC9qc3gtcnVudGltZVwiO1xuLy8gTm9ybWFsaXplcyBUcmFuc2l0aW9uIGNhbGxiYWNrcyB3aGVuIG5vZGVSZWYgaXMgdXNlZC5cbmNvbnN0IFRyYW5zaXRpb25XcmFwcGVyID0gLyojX19QVVJFX18qL1JlYWN0LmZvcndhcmRSZWYoKHtcbiAgb25FbnRlcixcbiAgb25FbnRlcmluZyxcbiAgb25FbnRlcmVkLFxuICBvbkV4aXQsXG4gIG9uRXhpdGluZyxcbiAgb25FeGl0ZWQsXG4gIGFkZEVuZExpc3RlbmVyLFxuICBjaGlsZHJlbixcbiAgY2hpbGRSZWYsXG4gIC4uLnByb3BzXG59LCByZWYpID0+IHtcbiAgY29uc3Qgbm9kZVJlZiA9IHVzZVJlZihudWxsKTtcbiAgY29uc3QgbWVyZ2VkUmVmID0gdXNlTWVyZ2VkUmVmcyhub2RlUmVmLCBjaGlsZFJlZik7XG4gIGNvbnN0IGF0dGFjaFJlZiA9IHIgPT4ge1xuICAgIG1lcmdlZFJlZihzYWZlRmluZERPTU5vZGUocikpO1xuICB9O1xuICBjb25zdCBub3JtYWxpemUgPSBjYWxsYmFjayA9PiBwYXJhbSA9PiB7XG4gICAgaWYgKGNhbGxiYWNrICYmIG5vZGVSZWYuY3VycmVudCkge1xuICAgICAgY2FsbGJhY2sobm9kZVJlZi5jdXJyZW50LCBwYXJhbSk7XG4gICAgfVxuICB9O1xuXG4gIC8qIGVzbGludC1kaXNhYmxlIHJlYWN0LWhvb2tzL2V4aGF1c3RpdmUtZGVwcyAqL1xuICBjb25zdCBoYW5kbGVFbnRlciA9IHVzZUNhbGxiYWNrKG5vcm1hbGl6ZShvbkVudGVyKSwgW29uRW50ZXJdKTtcbiAgY29uc3QgaGFuZGxlRW50ZXJpbmcgPSB1c2VDYWxsYmFjayhub3JtYWxpemUob25FbnRlcmluZyksIFtvbkVudGVyaW5nXSk7XG4gIGNvbnN0IGhhbmRsZUVudGVyZWQgPSB1c2VDYWxsYmFjayhub3JtYWxpemUob25FbnRlcmVkKSwgW29uRW50ZXJlZF0pO1xuICBjb25zdCBoYW5kbGVFeGl0ID0gdXNlQ2FsbGJhY2sobm9ybWFsaXplKG9uRXhpdCksIFtvbkV4aXRdKTtcbiAgY29uc3QgaGFuZGxlRXhpdGluZyA9IHVzZUNhbGxiYWNrKG5vcm1hbGl6ZShvbkV4aXRpbmcpLCBbb25FeGl0aW5nXSk7XG4gIGNvbnN0IGhhbmRsZUV4aXRlZCA9IHVzZUNhbGxiYWNrKG5vcm1hbGl6ZShvbkV4aXRlZCksIFtvbkV4aXRlZF0pO1xuICBjb25zdCBoYW5kbGVBZGRFbmRMaXN0ZW5lciA9IHVzZUNhbGxiYWNrKG5vcm1hbGl6ZShhZGRFbmRMaXN0ZW5lciksIFthZGRFbmRMaXN0ZW5lcl0pO1xuICAvKiBlc2xpbnQtZW5hYmxlIHJlYWN0LWhvb2tzL2V4aGF1c3RpdmUtZGVwcyAqL1xuXG4gIHJldHVybiAvKiNfX1BVUkVfXyovX2pzeChUcmFuc2l0aW9uLCB7XG4gICAgcmVmOiByZWYsXG4gICAgLi4ucHJvcHMsXG4gICAgb25FbnRlcjogaGFuZGxlRW50ZXIsXG4gICAgb25FbnRlcmVkOiBoYW5kbGVFbnRlcmVkLFxuICAgIG9uRW50ZXJpbmc6IGhhbmRsZUVudGVyaW5nLFxuICAgIG9uRXhpdDogaGFuZGxlRXhpdCxcbiAgICBvbkV4aXRlZDogaGFuZGxlRXhpdGVkLFxuICAgIG9uRXhpdGluZzogaGFuZGxlRXhpdGluZyxcbiAgICBhZGRFbmRMaXN0ZW5lcjogaGFuZGxlQWRkRW5kTGlzdGVuZXIsXG4gICAgbm9kZVJlZjogbm9kZVJlZixcbiAgICBjaGlsZHJlbjogdHlwZW9mIGNoaWxkcmVuID09PSAnZnVuY3Rpb24nID8gKHN0YXR1cywgaW5uZXJQcm9wcykgPT4gY2hpbGRyZW4oc3RhdHVzLCB7XG4gICAgICAuLi5pbm5lclByb3BzLFxuICAgICAgcmVmOiBhdHRhY2hSZWZcbiAgICB9KSA6IC8qI19fUFVSRV9fKi9SZWFjdC5jbG9uZUVsZW1lbnQoY2hpbGRyZW4sIHtcbiAgICAgIHJlZjogYXR0YWNoUmVmXG4gICAgfSlcbiAgfSk7XG59KTtcbmV4cG9ydCBkZWZhdWx0IFRyYW5zaXRpb25XcmFwcGVyOyIsImltcG9ydCBjbGFzc05hbWVzIGZyb20gJ2NsYXNzbmFtZXMnO1xuaW1wb3J0IGNzcyBmcm9tICdkb20taGVscGVycy9jc3MnO1xuaW1wb3J0IFJlYWN0LCB7IHVzZU1lbW8gfSBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyBFTlRFUkVELCBFTlRFUklORywgRVhJVEVELCBFWElUSU5HIH0gZnJvbSAncmVhY3QtdHJhbnNpdGlvbi1ncm91cC9UcmFuc2l0aW9uJztcbmltcG9ydCB0cmFuc2l0aW9uRW5kTGlzdGVuZXIgZnJvbSAnLi90cmFuc2l0aW9uRW5kTGlzdGVuZXInO1xuaW1wb3J0IGNyZWF0ZUNoYWluZWRGdW5jdGlvbiBmcm9tICcuL2NyZWF0ZUNoYWluZWRGdW5jdGlvbic7XG5pbXBvcnQgdHJpZ2dlckJyb3dzZXJSZWZsb3cgZnJvbSAnLi90cmlnZ2VyQnJvd3NlclJlZmxvdyc7XG5pbXBvcnQgVHJhbnNpdGlvbldyYXBwZXIgZnJvbSAnLi9UcmFuc2l0aW9uV3JhcHBlcic7XG5pbXBvcnQgeyBqc3ggYXMgX2pzeCB9IGZyb20gXCJyZWFjdC9qc3gtcnVudGltZVwiO1xuY29uc3QgTUFSR0lOUyA9IHtcbiAgaGVpZ2h0OiBbJ21hcmdpblRvcCcsICdtYXJnaW5Cb3R0b20nXSxcbiAgd2lkdGg6IFsnbWFyZ2luTGVmdCcsICdtYXJnaW5SaWdodCddXG59O1xuZnVuY3Rpb24gZ2V0RGVmYXVsdERpbWVuc2lvblZhbHVlKGRpbWVuc2lvbiwgZWxlbSkge1xuICBjb25zdCBvZmZzZXQgPSBgb2Zmc2V0JHtkaW1lbnNpb25bMF0udG9VcHBlckNhc2UoKX0ke2RpbWVuc2lvbi5zbGljZSgxKX1gO1xuICBjb25zdCB2YWx1ZSA9IGVsZW1bb2Zmc2V0XTtcbiAgY29uc3QgbWFyZ2lucyA9IE1BUkdJTlNbZGltZW5zaW9uXTtcbiAgcmV0dXJuIHZhbHVlICtcbiAgLy8gQHRzLWlnbm9yZVxuICBwYXJzZUludChjc3MoZWxlbSwgbWFyZ2luc1swXSksIDEwKSArXG4gIC8vIEB0cy1pZ25vcmVcbiAgcGFyc2VJbnQoY3NzKGVsZW0sIG1hcmdpbnNbMV0pLCAxMCk7XG59XG5jb25zdCBjb2xsYXBzZVN0eWxlcyA9IHtcbiAgW0VYSVRFRF06ICdjb2xsYXBzZScsXG4gIFtFWElUSU5HXTogJ2NvbGxhcHNpbmcnLFxuICBbRU5URVJJTkddOiAnY29sbGFwc2luZycsXG4gIFtFTlRFUkVEXTogJ2NvbGxhcHNlIHNob3cnXG59O1xuY29uc3QgZGVmYXVsdFByb3BzID0ge1xuICBpbjogZmFsc2UsXG4gIHRpbWVvdXQ6IDMwMCxcbiAgbW91bnRPbkVudGVyOiBmYWxzZSxcbiAgdW5tb3VudE9uRXhpdDogZmFsc2UsXG4gIGFwcGVhcjogZmFsc2UsXG4gIGdldERpbWVuc2lvblZhbHVlOiBnZXREZWZhdWx0RGltZW5zaW9uVmFsdWVcbn07XG5jb25zdCBDb2xsYXBzZSA9IC8qI19fUFVSRV9fKi9SZWFjdC5mb3J3YXJkUmVmKCh7XG4gIG9uRW50ZXIsXG4gIG9uRW50ZXJpbmcsXG4gIG9uRW50ZXJlZCxcbiAgb25FeGl0LFxuICBvbkV4aXRpbmcsXG4gIGNsYXNzTmFtZSxcbiAgY2hpbGRyZW4sXG4gIGRpbWVuc2lvbiA9ICdoZWlnaHQnLFxuICBnZXREaW1lbnNpb25WYWx1ZSA9IGdldERlZmF1bHREaW1lbnNpb25WYWx1ZSxcbiAgLi4ucHJvcHNcbn0sIHJlZikgPT4ge1xuICAvKiBDb21wdXRlIGRpbWVuc2lvbiAqL1xuICBjb25zdCBjb21wdXRlZERpbWVuc2lvbiA9IHR5cGVvZiBkaW1lbnNpb24gPT09ICdmdW5jdGlvbicgPyBkaW1lbnNpb24oKSA6IGRpbWVuc2lvbjtcblxuICAvKiAtLSBFeHBhbmRpbmcgLS0gKi9cbiAgY29uc3QgaGFuZGxlRW50ZXIgPSB1c2VNZW1vKCgpID0+IGNyZWF0ZUNoYWluZWRGdW5jdGlvbihlbGVtID0+IHtcbiAgICBlbGVtLnN0eWxlW2NvbXB1dGVkRGltZW5zaW9uXSA9ICcwJztcbiAgfSwgb25FbnRlciksIFtjb21wdXRlZERpbWVuc2lvbiwgb25FbnRlcl0pO1xuICBjb25zdCBoYW5kbGVFbnRlcmluZyA9IHVzZU1lbW8oKCkgPT4gY3JlYXRlQ2hhaW5lZEZ1bmN0aW9uKGVsZW0gPT4ge1xuICAgIGNvbnN0IHNjcm9sbCA9IGBzY3JvbGwke2NvbXB1dGVkRGltZW5zaW9uWzBdLnRvVXBwZXJDYXNlKCl9JHtjb21wdXRlZERpbWVuc2lvbi5zbGljZSgxKX1gO1xuICAgIGVsZW0uc3R5bGVbY29tcHV0ZWREaW1lbnNpb25dID0gYCR7ZWxlbVtzY3JvbGxdfXB4YDtcbiAgfSwgb25FbnRlcmluZyksIFtjb21wdXRlZERpbWVuc2lvbiwgb25FbnRlcmluZ10pO1xuICBjb25zdCBoYW5kbGVFbnRlcmVkID0gdXNlTWVtbygoKSA9PiBjcmVhdGVDaGFpbmVkRnVuY3Rpb24oZWxlbSA9PiB7XG4gICAgZWxlbS5zdHlsZVtjb21wdXRlZERpbWVuc2lvbl0gPSBudWxsO1xuICB9LCBvbkVudGVyZWQpLCBbY29tcHV0ZWREaW1lbnNpb24sIG9uRW50ZXJlZF0pO1xuXG4gIC8qIC0tIENvbGxhcHNpbmcgLS0gKi9cbiAgY29uc3QgaGFuZGxlRXhpdCA9IHVzZU1lbW8oKCkgPT4gY3JlYXRlQ2hhaW5lZEZ1bmN0aW9uKGVsZW0gPT4ge1xuICAgIGVsZW0uc3R5bGVbY29tcHV0ZWREaW1lbnNpb25dID0gYCR7Z2V0RGltZW5zaW9uVmFsdWUoY29tcHV0ZWREaW1lbnNpb24sIGVsZW0pfXB4YDtcbiAgICB0cmlnZ2VyQnJvd3NlclJlZmxvdyhlbGVtKTtcbiAgfSwgb25FeGl0KSwgW29uRXhpdCwgZ2V0RGltZW5zaW9uVmFsdWUsIGNvbXB1dGVkRGltZW5zaW9uXSk7XG4gIGNvbnN0IGhhbmRsZUV4aXRpbmcgPSB1c2VNZW1vKCgpID0+IGNyZWF0ZUNoYWluZWRGdW5jdGlvbihlbGVtID0+IHtcbiAgICBlbGVtLnN0eWxlW2NvbXB1dGVkRGltZW5zaW9uXSA9IG51bGw7XG4gIH0sIG9uRXhpdGluZyksIFtjb21wdXRlZERpbWVuc2lvbiwgb25FeGl0aW5nXSk7XG4gIHJldHVybiAvKiNfX1BVUkVfXyovX2pzeChUcmFuc2l0aW9uV3JhcHBlciwge1xuICAgIHJlZjogcmVmLFxuICAgIGFkZEVuZExpc3RlbmVyOiB0cmFuc2l0aW9uRW5kTGlzdGVuZXIsXG4gICAgLi4ucHJvcHMsXG4gICAgXCJhcmlhLWV4cGFuZGVkXCI6IHByb3BzLnJvbGUgPyBwcm9wcy5pbiA6IG51bGwsXG4gICAgb25FbnRlcjogaGFuZGxlRW50ZXIsXG4gICAgb25FbnRlcmluZzogaGFuZGxlRW50ZXJpbmcsXG4gICAgb25FbnRlcmVkOiBoYW5kbGVFbnRlcmVkLFxuICAgIG9uRXhpdDogaGFuZGxlRXhpdCxcbiAgICBvbkV4aXRpbmc6IGhhbmRsZUV4aXRpbmcsXG4gICAgY2hpbGRSZWY6IGNoaWxkcmVuLnJlZixcbiAgICBjaGlsZHJlbjogKHN0YXRlLCBpbm5lclByb3BzKSA9PiAvKiNfX1BVUkVfXyovUmVhY3QuY2xvbmVFbGVtZW50KGNoaWxkcmVuLCB7XG4gICAgICAuLi5pbm5lclByb3BzLFxuICAgICAgY2xhc3NOYW1lOiBjbGFzc05hbWVzKGNsYXNzTmFtZSwgY2hpbGRyZW4ucHJvcHMuY2xhc3NOYW1lLCBjb2xsYXBzZVN0eWxlc1tzdGF0ZV0sIGNvbXB1dGVkRGltZW5zaW9uID09PSAnd2lkdGgnICYmICdjb2xsYXBzZS1ob3Jpem9udGFsJylcbiAgICB9KVxuICB9KTtcbn0pO1xuXG4vLyBAdHMtaWdub3JlXG5cbi8vIEB0cy1pZ25vcmVcbkNvbGxhcHNlLmRlZmF1bHRQcm9wcyA9IGRlZmF1bHRQcm9wcztcbmV4cG9ydCBkZWZhdWx0IENvbGxhcHNlOyIsImltcG9ydCAqIGFzIFJlYWN0IGZyb20gJ3JlYWN0JztcbmV4cG9ydCBmdW5jdGlvbiBpc0FjY29yZGlvbkl0ZW1TZWxlY3RlZChhY3RpdmVFdmVudEtleSwgZXZlbnRLZXkpIHtcbiAgcmV0dXJuIEFycmF5LmlzQXJyYXkoYWN0aXZlRXZlbnRLZXkpID8gYWN0aXZlRXZlbnRLZXkuaW5jbHVkZXMoZXZlbnRLZXkpIDogYWN0aXZlRXZlbnRLZXkgPT09IGV2ZW50S2V5O1xufVxuY29uc3QgY29udGV4dCA9IC8qI19fUFVSRV9fKi9SZWFjdC5jcmVhdGVDb250ZXh0KHt9KTtcbmNvbnRleHQuZGlzcGxheU5hbWUgPSAnQWNjb3JkaW9uQ29udGV4dCc7XG5leHBvcnQgZGVmYXVsdCBjb250ZXh0OyIsImltcG9ydCBjbGFzc05hbWVzIGZyb20gJ2NsYXNzbmFtZXMnO1xuaW1wb3J0ICogYXMgUmVhY3QgZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsgdXNlQ29udGV4dCB9IGZyb20gJ3JlYWN0JztcbmltcG9ydCB7IHVzZUJvb3RzdHJhcFByZWZpeCB9IGZyb20gJy4vVGhlbWVQcm92aWRlcic7XG5pbXBvcnQgQ29sbGFwc2UgZnJvbSAnLi9Db2xsYXBzZSc7XG5pbXBvcnQgQWNjb3JkaW9uQ29udGV4dCwgeyBpc0FjY29yZGlvbkl0ZW1TZWxlY3RlZCB9IGZyb20gJy4vQWNjb3JkaW9uQ29udGV4dCc7XG5pbXBvcnQgeyBqc3ggYXMgX2pzeCB9IGZyb20gXCJyZWFjdC9qc3gtcnVudGltZVwiO1xuLyoqXG4gKiBUaGlzIGNvbXBvbmVudCBhY2NlcHRzIGFsbCBvZiBbYENvbGxhcHNlYCdzIHByb3BzXSgvdXRpbGl0aWVzL3RyYW5zaXRpb25zLyNjb2xsYXBzZS1wcm9wcykuXG4gKi9cbmNvbnN0IEFjY29yZGlvbkNvbGxhcHNlID0gLyojX19QVVJFX18qL1JlYWN0LmZvcndhcmRSZWYoKHtcbiAgYXM6IENvbXBvbmVudCA9ICdkaXYnLFxuICBic1ByZWZpeCxcbiAgY2xhc3NOYW1lLFxuICBjaGlsZHJlbixcbiAgZXZlbnRLZXksXG4gIC4uLnByb3BzXG59LCByZWYpID0+IHtcbiAgY29uc3Qge1xuICAgIGFjdGl2ZUV2ZW50S2V5XG4gIH0gPSB1c2VDb250ZXh0KEFjY29yZGlvbkNvbnRleHQpO1xuICBic1ByZWZpeCA9IHVzZUJvb3RzdHJhcFByZWZpeChic1ByZWZpeCwgJ2FjY29yZGlvbi1jb2xsYXBzZScpO1xuICByZXR1cm4gLyojX19QVVJFX18qL19qc3goQ29sbGFwc2UsIHtcbiAgICByZWY6IHJlZixcbiAgICBpbjogaXNBY2NvcmRpb25JdGVtU2VsZWN0ZWQoYWN0aXZlRXZlbnRLZXksIGV2ZW50S2V5KSxcbiAgICAuLi5wcm9wcyxcbiAgICBjbGFzc05hbWU6IGNsYXNzTmFtZXMoY2xhc3NOYW1lLCBic1ByZWZpeCksXG4gICAgY2hpbGRyZW46IC8qI19fUFVSRV9fKi9fanN4KENvbXBvbmVudCwge1xuICAgICAgY2hpbGRyZW46IFJlYWN0LkNoaWxkcmVuLm9ubHkoY2hpbGRyZW4pXG4gICAgfSlcbiAgfSk7XG59KTtcbkFjY29yZGlvbkNvbGxhcHNlLmRpc3BsYXlOYW1lID0gJ0FjY29yZGlvbkNvbGxhcHNlJztcbmV4cG9ydCBkZWZhdWx0IEFjY29yZGlvbkNvbGxhcHNlOyIsImltcG9ydCAqIGFzIFJlYWN0IGZyb20gJ3JlYWN0JztcbmNvbnN0IGNvbnRleHQgPSAvKiNfX1BVUkVfXyovUmVhY3QuY3JlYXRlQ29udGV4dCh7XG4gIGV2ZW50S2V5OiAnJ1xufSk7XG5jb250ZXh0LmRpc3BsYXlOYW1lID0gJ0FjY29yZGlvbkl0ZW1Db250ZXh0JztcbmV4cG9ydCBkZWZhdWx0IGNvbnRleHQ7IiwiaW1wb3J0IGNsYXNzTmFtZXMgZnJvbSAnY2xhc3NuYW1lcyc7XG5pbXBvcnQgKiBhcyBSZWFjdCBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyB1c2VDb250ZXh0IH0gZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsgdXNlQm9vdHN0cmFwUHJlZml4IH0gZnJvbSAnLi9UaGVtZVByb3ZpZGVyJztcbmltcG9ydCBBY2NvcmRpb25Db2xsYXBzZSBmcm9tICcuL0FjY29yZGlvbkNvbGxhcHNlJztcbmltcG9ydCBBY2NvcmRpb25JdGVtQ29udGV4dCBmcm9tICcuL0FjY29yZGlvbkl0ZW1Db250ZXh0JztcbmltcG9ydCB7IGpzeCBhcyBfanN4IH0gZnJvbSBcInJlYWN0L2pzeC1ydW50aW1lXCI7XG5jb25zdCBBY2NvcmRpb25Cb2R5ID0gLyojX19QVVJFX18qL1JlYWN0LmZvcndhcmRSZWYoKHtcbiAgLy8gTmVlZCB0byBkZWZpbmUgdGhlIGRlZmF1bHQgXCJhc1wiIGR1cmluZyBwcm9wIGRlc3RydWN0dXJpbmcgdG8gYmUgY29tcGF0aWJsZSB3aXRoIHN0eWxlZC1jb21wb25lbnRzIGdpdGh1Yi5jb20vcmVhY3QtYm9vdHN0cmFwL3JlYWN0LWJvb3RzdHJhcC9pc3N1ZXMvMzU5NVxuICBhczogQ29tcG9uZW50ID0gJ2RpdicsXG4gIGJzUHJlZml4LFxuICBjbGFzc05hbWUsXG4gIG9uRW50ZXIsXG4gIG9uRW50ZXJpbmcsXG4gIG9uRW50ZXJlZCxcbiAgb25FeGl0LFxuICBvbkV4aXRpbmcsXG4gIG9uRXhpdGVkLFxuICAuLi5wcm9wc1xufSwgcmVmKSA9PiB7XG4gIGJzUHJlZml4ID0gdXNlQm9vdHN0cmFwUHJlZml4KGJzUHJlZml4LCAnYWNjb3JkaW9uLWJvZHknKTtcbiAgY29uc3Qge1xuICAgIGV2ZW50S2V5XG4gIH0gPSB1c2VDb250ZXh0KEFjY29yZGlvbkl0ZW1Db250ZXh0KTtcbiAgcmV0dXJuIC8qI19fUFVSRV9fKi9fanN4KEFjY29yZGlvbkNvbGxhcHNlLCB7XG4gICAgZXZlbnRLZXk6IGV2ZW50S2V5LFxuICAgIG9uRW50ZXI6IG9uRW50ZXIsXG4gICAgb25FbnRlcmluZzogb25FbnRlcmluZyxcbiAgICBvbkVudGVyZWQ6IG9uRW50ZXJlZCxcbiAgICBvbkV4aXQ6IG9uRXhpdCxcbiAgICBvbkV4aXRpbmc6IG9uRXhpdGluZyxcbiAgICBvbkV4aXRlZDogb25FeGl0ZWQsXG4gICAgY2hpbGRyZW46IC8qI19fUFVSRV9fKi9fanN4KENvbXBvbmVudCwge1xuICAgICAgcmVmOiByZWYsXG4gICAgICAuLi5wcm9wcyxcbiAgICAgIGNsYXNzTmFtZTogY2xhc3NOYW1lcyhjbGFzc05hbWUsIGJzUHJlZml4KVxuICAgIH0pXG4gIH0pO1xufSk7XG5BY2NvcmRpb25Cb2R5LmRpc3BsYXlOYW1lID0gJ0FjY29yZGlvbkJvZHknO1xuZXhwb3J0IGRlZmF1bHQgQWNjb3JkaW9uQm9keTsiLCJpbXBvcnQgKiBhcyBSZWFjdCBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyB1c2VDb250ZXh0IH0gZnJvbSAncmVhY3QnO1xuaW1wb3J0IGNsYXNzTmFtZXMgZnJvbSAnY2xhc3NuYW1lcyc7XG5pbXBvcnQgQWNjb3JkaW9uQ29udGV4dCwgeyBpc0FjY29yZGlvbkl0ZW1TZWxlY3RlZCB9IGZyb20gJy4vQWNjb3JkaW9uQ29udGV4dCc7XG5pbXBvcnQgQWNjb3JkaW9uSXRlbUNvbnRleHQgZnJvbSAnLi9BY2NvcmRpb25JdGVtQ29udGV4dCc7XG5pbXBvcnQgeyB1c2VCb290c3RyYXBQcmVmaXggfSBmcm9tICcuL1RoZW1lUHJvdmlkZXInO1xuaW1wb3J0IHsganN4IGFzIF9qc3ggfSBmcm9tIFwicmVhY3QvanN4LXJ1bnRpbWVcIjtcbmV4cG9ydCBmdW5jdGlvbiB1c2VBY2NvcmRpb25CdXR0b24oZXZlbnRLZXksIG9uQ2xpY2spIHtcbiAgY29uc3Qge1xuICAgIGFjdGl2ZUV2ZW50S2V5LFxuICAgIG9uU2VsZWN0LFxuICAgIGFsd2F5c09wZW5cbiAgfSA9IHVzZUNvbnRleHQoQWNjb3JkaW9uQ29udGV4dCk7XG4gIHJldHVybiBlID0+IHtcbiAgICAvKlxuICAgICAgQ29tcGFyZSB0aGUgZXZlbnQga2V5IGluIGNvbnRleHQgd2l0aCB0aGUgZ2l2ZW4gZXZlbnQga2V5LlxuICAgICAgSWYgdGhleSBhcmUgdGhlIHNhbWUsIHRoZW4gY29sbGFwc2UgdGhlIGNvbXBvbmVudC5cbiAgICAqL1xuICAgIGxldCBldmVudEtleVBhc3NlZCA9IGV2ZW50S2V5ID09PSBhY3RpdmVFdmVudEtleSA/IG51bGwgOiBldmVudEtleTtcbiAgICBpZiAoYWx3YXlzT3Blbikge1xuICAgICAgaWYgKEFycmF5LmlzQXJyYXkoYWN0aXZlRXZlbnRLZXkpKSB7XG4gICAgICAgIGlmIChhY3RpdmVFdmVudEtleS5pbmNsdWRlcyhldmVudEtleSkpIHtcbiAgICAgICAgICBldmVudEtleVBhc3NlZCA9IGFjdGl2ZUV2ZW50S2V5LmZpbHRlcihrID0+IGsgIT09IGV2ZW50S2V5KTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBldmVudEtleVBhc3NlZCA9IFsuLi5hY3RpdmVFdmVudEtleSwgZXZlbnRLZXldO1xuICAgICAgICB9XG4gICAgICB9IGVsc2Uge1xuICAgICAgICAvLyBhY3RpdmVFdmVudEtleSBpcyB1bmRlZmluZWQuXG4gICAgICAgIGV2ZW50S2V5UGFzc2VkID0gW2V2ZW50S2V5XTtcbiAgICAgIH1cbiAgICB9XG4gICAgb25TZWxlY3QgPT0gbnVsbCA/IHZvaWQgMCA6IG9uU2VsZWN0KGV2ZW50S2V5UGFzc2VkLCBlKTtcbiAgICBvbkNsaWNrID09IG51bGwgPyB2b2lkIDAgOiBvbkNsaWNrKGUpO1xuICB9O1xufVxuY29uc3QgQWNjb3JkaW9uQnV0dG9uID0gLyojX19QVVJFX18qL1JlYWN0LmZvcndhcmRSZWYoKHtcbiAgLy8gTmVlZCB0byBkZWZpbmUgdGhlIGRlZmF1bHQgXCJhc1wiIGR1cmluZyBwcm9wIGRlc3RydWN0dXJpbmcgdG8gYmUgY29tcGF0aWJsZSB3aXRoIHN0eWxlZC1jb21wb25lbnRzIGdpdGh1Yi5jb20vcmVhY3QtYm9vdHN0cmFwL3JlYWN0LWJvb3RzdHJhcC9pc3N1ZXMvMzU5NVxuICBhczogQ29tcG9uZW50ID0gJ2J1dHRvbicsXG4gIGJzUHJlZml4LFxuICBjbGFzc05hbWUsXG4gIG9uQ2xpY2ssXG4gIC4uLnByb3BzXG59LCByZWYpID0+IHtcbiAgYnNQcmVmaXggPSB1c2VCb290c3RyYXBQcmVmaXgoYnNQcmVmaXgsICdhY2NvcmRpb24tYnV0dG9uJyk7XG4gIGNvbnN0IHtcbiAgICBldmVudEtleVxuICB9ID0gdXNlQ29udGV4dChBY2NvcmRpb25JdGVtQ29udGV4dCk7XG4gIGNvbnN0IGFjY29yZGlvbk9uQ2xpY2sgPSB1c2VBY2NvcmRpb25CdXR0b24oZXZlbnRLZXksIG9uQ2xpY2spO1xuICBjb25zdCB7XG4gICAgYWN0aXZlRXZlbnRLZXlcbiAgfSA9IHVzZUNvbnRleHQoQWNjb3JkaW9uQ29udGV4dCk7XG4gIGlmIChDb21wb25lbnQgPT09ICdidXR0b24nKSB7XG4gICAgcHJvcHMudHlwZSA9ICdidXR0b24nO1xuICB9XG4gIHJldHVybiAvKiNfX1BVUkVfXyovX2pzeChDb21wb25lbnQsIHtcbiAgICByZWY6IHJlZixcbiAgICBvbkNsaWNrOiBhY2NvcmRpb25PbkNsaWNrLFxuICAgIC4uLnByb3BzLFxuICAgIFwiYXJpYS1leHBhbmRlZFwiOiBldmVudEtleSA9PT0gYWN0aXZlRXZlbnRLZXksXG4gICAgY2xhc3NOYW1lOiBjbGFzc05hbWVzKGNsYXNzTmFtZSwgYnNQcmVmaXgsICFpc0FjY29yZGlvbkl0ZW1TZWxlY3RlZChhY3RpdmVFdmVudEtleSwgZXZlbnRLZXkpICYmICdjb2xsYXBzZWQnKVxuICB9KTtcbn0pO1xuQWNjb3JkaW9uQnV0dG9uLmRpc3BsYXlOYW1lID0gJ0FjY29yZGlvbkJ1dHRvbic7XG5leHBvcnQgZGVmYXVsdCBBY2NvcmRpb25CdXR0b247IiwiaW1wb3J0IGNsYXNzTmFtZXMgZnJvbSAnY2xhc3NuYW1lcyc7XG5pbXBvcnQgKiBhcyBSZWFjdCBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyB1c2VCb290c3RyYXBQcmVmaXggfSBmcm9tICcuL1RoZW1lUHJvdmlkZXInO1xuaW1wb3J0IEFjY29yZGlvbkJ1dHRvbiBmcm9tICcuL0FjY29yZGlvbkJ1dHRvbic7XG5pbXBvcnQgeyBqc3ggYXMgX2pzeCB9IGZyb20gXCJyZWFjdC9qc3gtcnVudGltZVwiO1xuY29uc3QgQWNjb3JkaW9uSGVhZGVyID0gLyojX19QVVJFX18qL1JlYWN0LmZvcndhcmRSZWYoKHtcbiAgLy8gTmVlZCB0byBkZWZpbmUgdGhlIGRlZmF1bHQgXCJhc1wiIGR1cmluZyBwcm9wIGRlc3RydWN0dXJpbmcgdG8gYmUgY29tcGF0aWJsZSB3aXRoIHN0eWxlZC1jb21wb25lbnRzIGdpdGh1Yi5jb20vcmVhY3QtYm9vdHN0cmFwL3JlYWN0LWJvb3RzdHJhcC9pc3N1ZXMvMzU5NVxuICBhczogQ29tcG9uZW50ID0gJ2gyJyxcbiAgYnNQcmVmaXgsXG4gIGNsYXNzTmFtZSxcbiAgY2hpbGRyZW4sXG4gIG9uQ2xpY2ssXG4gIC4uLnByb3BzXG59LCByZWYpID0+IHtcbiAgYnNQcmVmaXggPSB1c2VCb290c3RyYXBQcmVmaXgoYnNQcmVmaXgsICdhY2NvcmRpb24taGVhZGVyJyk7XG4gIHJldHVybiAvKiNfX1BVUkVfXyovX2pzeChDb21wb25lbnQsIHtcbiAgICByZWY6IHJlZixcbiAgICAuLi5wcm9wcyxcbiAgICBjbGFzc05hbWU6IGNsYXNzTmFtZXMoY2xhc3NOYW1lLCBic1ByZWZpeCksXG4gICAgY2hpbGRyZW46IC8qI19fUFVSRV9fKi9fanN4KEFjY29yZGlvbkJ1dHRvbiwge1xuICAgICAgb25DbGljazogb25DbGljayxcbiAgICAgIGNoaWxkcmVuOiBjaGlsZHJlblxuICAgIH0pXG4gIH0pO1xufSk7XG5BY2NvcmRpb25IZWFkZXIuZGlzcGxheU5hbWUgPSAnQWNjb3JkaW9uSGVhZGVyJztcbmV4cG9ydCBkZWZhdWx0IEFjY29yZGlvbkhlYWRlcjsiLCJpbXBvcnQgY2xhc3NOYW1lcyBmcm9tICdjbGFzc25hbWVzJztcbmltcG9ydCAqIGFzIFJlYWN0IGZyb20gJ3JlYWN0JztcbmltcG9ydCB7IHVzZU1lbW8gfSBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyB1c2VCb290c3RyYXBQcmVmaXggfSBmcm9tICcuL1RoZW1lUHJvdmlkZXInO1xuaW1wb3J0IEFjY29yZGlvbkl0ZW1Db250ZXh0IGZyb20gJy4vQWNjb3JkaW9uSXRlbUNvbnRleHQnO1xuaW1wb3J0IHsganN4IGFzIF9qc3ggfSBmcm9tIFwicmVhY3QvanN4LXJ1bnRpbWVcIjtcbmNvbnN0IEFjY29yZGlvbkl0ZW0gPSAvKiNfX1BVUkVfXyovUmVhY3QuZm9yd2FyZFJlZigoe1xuICAvLyBOZWVkIHRvIGRlZmluZSB0aGUgZGVmYXVsdCBcImFzXCIgZHVyaW5nIHByb3AgZGVzdHJ1Y3R1cmluZyB0byBiZSBjb21wYXRpYmxlIHdpdGggc3R5bGVkLWNvbXBvbmVudHMgZ2l0aHViLmNvbS9yZWFjdC1ib290c3RyYXAvcmVhY3QtYm9vdHN0cmFwL2lzc3Vlcy8zNTk1XG4gIGFzOiBDb21wb25lbnQgPSAnZGl2JyxcbiAgYnNQcmVmaXgsXG4gIGNsYXNzTmFtZSxcbiAgZXZlbnRLZXksXG4gIC4uLnByb3BzXG59LCByZWYpID0+IHtcbiAgYnNQcmVmaXggPSB1c2VCb290c3RyYXBQcmVmaXgoYnNQcmVmaXgsICdhY2NvcmRpb24taXRlbScpO1xuICBjb25zdCBjb250ZXh0VmFsdWUgPSB1c2VNZW1vKCgpID0+ICh7XG4gICAgZXZlbnRLZXlcbiAgfSksIFtldmVudEtleV0pO1xuICByZXR1cm4gLyojX19QVVJFX18qL19qc3goQWNjb3JkaW9uSXRlbUNvbnRleHQuUHJvdmlkZXIsIHtcbiAgICB2YWx1ZTogY29udGV4dFZhbHVlLFxuICAgIGNoaWxkcmVuOiAvKiNfX1BVUkVfXyovX2pzeChDb21wb25lbnQsIHtcbiAgICAgIHJlZjogcmVmLFxuICAgICAgLi4ucHJvcHMsXG4gICAgICBjbGFzc05hbWU6IGNsYXNzTmFtZXMoY2xhc3NOYW1lLCBic1ByZWZpeClcbiAgICB9KVxuICB9KTtcbn0pO1xuQWNjb3JkaW9uSXRlbS5kaXNwbGF5TmFtZSA9ICdBY2NvcmRpb25JdGVtJztcbmV4cG9ydCBkZWZhdWx0IEFjY29yZGlvbkl0ZW07IiwiaW1wb3J0IGNsYXNzTmFtZXMgZnJvbSAnY2xhc3NuYW1lcyc7XG5pbXBvcnQgKiBhcyBSZWFjdCBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyB1c2VNZW1vIH0gZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsgdXNlVW5jb250cm9sbGVkIH0gZnJvbSAndW5jb250cm9sbGFibGUnO1xuaW1wb3J0IHsgdXNlQm9vdHN0cmFwUHJlZml4IH0gZnJvbSAnLi9UaGVtZVByb3ZpZGVyJztcbmltcG9ydCBBY2NvcmRpb25Cb2R5IGZyb20gJy4vQWNjb3JkaW9uQm9keSc7XG5pbXBvcnQgQWNjb3JkaW9uQnV0dG9uIGZyb20gJy4vQWNjb3JkaW9uQnV0dG9uJztcbmltcG9ydCBBY2NvcmRpb25Db2xsYXBzZSBmcm9tICcuL0FjY29yZGlvbkNvbGxhcHNlJztcbmltcG9ydCBBY2NvcmRpb25Db250ZXh0IGZyb20gJy4vQWNjb3JkaW9uQ29udGV4dCc7XG5pbXBvcnQgQWNjb3JkaW9uSGVhZGVyIGZyb20gJy4vQWNjb3JkaW9uSGVhZGVyJztcbmltcG9ydCBBY2NvcmRpb25JdGVtIGZyb20gJy4vQWNjb3JkaW9uSXRlbSc7XG5pbXBvcnQgeyBqc3ggYXMgX2pzeCB9IGZyb20gXCJyZWFjdC9qc3gtcnVudGltZVwiO1xuY29uc3QgQWNjb3JkaW9uID0gLyojX19QVVJFX18qL1JlYWN0LmZvcndhcmRSZWYoKHByb3BzLCByZWYpID0+IHtcbiAgY29uc3Qge1xuICAgIC8vIE5lZWQgdG8gZGVmaW5lIHRoZSBkZWZhdWx0IFwiYXNcIiBkdXJpbmcgcHJvcCBkZXN0cnVjdHVyaW5nIHRvIGJlIGNvbXBhdGlibGUgd2l0aCBzdHlsZWQtY29tcG9uZW50cyBnaXRodWIuY29tL3JlYWN0LWJvb3RzdHJhcC9yZWFjdC1ib290c3RyYXAvaXNzdWVzLzM1OTVcbiAgICBhczogQ29tcG9uZW50ID0gJ2RpdicsXG4gICAgYWN0aXZlS2V5LFxuICAgIGJzUHJlZml4LFxuICAgIGNsYXNzTmFtZSxcbiAgICBvblNlbGVjdCxcbiAgICBmbHVzaCxcbiAgICBhbHdheXNPcGVuLFxuICAgIC4uLmNvbnRyb2xsZWRQcm9wc1xuICB9ID0gdXNlVW5jb250cm9sbGVkKHByb3BzLCB7XG4gICAgYWN0aXZlS2V5OiAnb25TZWxlY3QnXG4gIH0pO1xuICBjb25zdCBwcmVmaXggPSB1c2VCb290c3RyYXBQcmVmaXgoYnNQcmVmaXgsICdhY2NvcmRpb24nKTtcbiAgY29uc3QgY29udGV4dFZhbHVlID0gdXNlTWVtbygoKSA9PiAoe1xuICAgIGFjdGl2ZUV2ZW50S2V5OiBhY3RpdmVLZXksXG4gICAgb25TZWxlY3QsXG4gICAgYWx3YXlzT3BlblxuICB9KSwgW2FjdGl2ZUtleSwgb25TZWxlY3QsIGFsd2F5c09wZW5dKTtcbiAgcmV0dXJuIC8qI19fUFVSRV9fKi9fanN4KEFjY29yZGlvbkNvbnRleHQuUHJvdmlkZXIsIHtcbiAgICB2YWx1ZTogY29udGV4dFZhbHVlLFxuICAgIGNoaWxkcmVuOiAvKiNfX1BVUkVfXyovX2pzeChDb21wb25lbnQsIHtcbiAgICAgIHJlZjogcmVmLFxuICAgICAgLi4uY29udHJvbGxlZFByb3BzLFxuICAgICAgY2xhc3NOYW1lOiBjbGFzc05hbWVzKGNsYXNzTmFtZSwgcHJlZml4LCBmbHVzaCAmJiBgJHtwcmVmaXh9LWZsdXNoYClcbiAgICB9KVxuICB9KTtcbn0pO1xuQWNjb3JkaW9uLmRpc3BsYXlOYW1lID0gJ0FjY29yZGlvbic7XG5leHBvcnQgZGVmYXVsdCBPYmplY3QuYXNzaWduKEFjY29yZGlvbiwge1xuICBCdXR0b246IEFjY29yZGlvbkJ1dHRvbixcbiAgQ29sbGFwc2U6IEFjY29yZGlvbkNvbGxhcHNlLFxuICBJdGVtOiBBY2NvcmRpb25JdGVtLFxuICBIZWFkZXI6IEFjY29yZGlvbkhlYWRlcixcbiAgQm9keTogQWNjb3JkaW9uQm9keVxufSk7IiwiaW1wb3J0IHsgQ29tcG9uZW50LCBSZWFjdE5vZGUsIGNyZWF0ZUVsZW1lbnQgfSBmcm9tIFwicmVhY3RcIjtcblxuaW1wb3J0IHsgQWNjb3JkaWFuQ29udGFpbmVyUHJvcHMgfSBmcm9tIFwiLi4vdHlwaW5ncy9BY2NvcmRpYW5Qcm9wc1wiO1xuXG5pbXBvcnQgXCIuL3VpL0FjY29yZGlhbi5jc3NcIjtcblxuaW1wb3J0IEFjY29yZGlvbiBmcm9tIFwicmVhY3QtYm9vdHN0cmFwL0FjY29yZGlvblwiO1xuXG5leHBvcnQgY2xhc3MgQWNjb3JkaWFuIGV4dGVuZHMgQ29tcG9uZW50PEFjY29yZGlhbkNvbnRhaW5lclByb3BzPiB7XG5cbiAgICBwdWJsaWMgaGVhZGVyID0gdGhpcy5wcm9wcy5oZWFkaW5nPy52YWx1ZSA/IHRoaXMucHJvcHMuaGVhZGluZz8udmFsdWUgOiBcIiBcIjtcbiAgXG5cbiAgICBoYW5kbGVFbnRlciA9ICgpPT57XG4gICAgICAgIGlmICh0aGlzLnByb3BzLm9uRW50ZXIgJiYgdGhpcy5wcm9wcy5vbkVudGVyLmNhbkV4ZWN1dGUpIHtcbiAgICAgICAgICAgIHRoaXMucHJvcHMub25FbnRlci5leGVjdXRlKCk7XG4gICAgICAgIH1cbiAgICB9XG5cbiAgICBoYW5kbGVFeGl0ID0gKCk9PntcbiAgICAgICAgaWYgKHRoaXMucHJvcHMub25FeGl0ICYmIHRoaXMucHJvcHMub25FeGl0LmNhbkV4ZWN1dGUpIHtcbiAgICAgICAgICAgIHRoaXMucHJvcHMub25FeGl0LmV4ZWN1dGUoKTtcbiAgICAgICAgfVxuICAgIH1cblxuICAgIGhhbmRsZXIgPSAoKT0+e1xuICAgICAgICBpZih0aGlzLnByb3BzLmJvb2xlYW4pe1xuICAgICAgICAgICAgaWYgKHRoaXMucHJvcHMub25FbnRlciAmJiB0aGlzLnByb3BzLm9uRW50ZXIuY2FuRXhlY3V0ZSkge1xuICAgICAgICAgICAgICAgIHRoaXMucHJvcHMub25FbnRlci5leGVjdXRlKCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gXCIwXCI7XG4gICAgICAgIH1lbHNle1xuICAgICAgICAgICAgcmV0dXJuIFwiXCI7XG4gICAgICAgIH1cbiAgICB9XG5cbiAgICBoYW5kbGVkZWZhdWx0b3BlbiA6IGFueSA9ICB0aGlzLmhhbmRsZXI7XG5cbiAgICByZW5kZXIoKTogUmVhY3ROb2RlIHtcbiAgICAgICAgdGhpcy5oZWFkZXIgPSB0aGlzLnByb3BzLmhlYWRpbmc/LnZhbHVlID8gdGhpcy5wcm9wcy5oZWFkaW5nPy52YWx1ZSA6IFwiIFwiO1xuXG4gICAgICAgIHJldHVybiAoXG4gICAgICAgICAgICAgICAgPEFjY29yZGlvbiBkZWZhdWx0QWN0aXZlS2V5PXt0aGlzLmhhbmRsZWRlZmF1bHRvcGVufT5cbiAgICAgICAgICAgICAgICAgICAgPEFjY29yZGlvbi5JdGVtIGV2ZW50S2V5PVwiMFwiPlxuICAgICAgICAgICAgICAgICAgICAgICAgPEFjY29yZGlvbi5IZWFkZXIgY2xhc3NOYW1lPVwiQWNjb3JkaWFuSGVhZGVyXCI+e3RoaXMuaGVhZGVyfTwvQWNjb3JkaW9uLkhlYWRlcj5cbiAgICAgICAgICAgICAgICAgICAgICAgIDxBY2NvcmRpb24uQm9keSBvbkVudGVyPXt0aGlzLmhhbmRsZUVudGVyfSBvbkV4aXQ9e3RoaXMuaGFuZGxlRXhpdH0+XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAge3RoaXMucHJvcHMuY29udGVudH1cbiAgICAgICAgICAgICAgICAgICAgICAgIDwvQWNjb3JkaW9uLkJvZHk+XG4gICAgICAgICAgICAgICAgICAgIDwvQWNjb3JkaW9uLkl0ZW0+XG4gICAgICAgICAgICAgICAgPC9BY2NvcmRpb24+XG4gICAgICAgICk7XG4gICAgfVxufVxuIl0sIm5hbWVzIjpbImhhc093biIsImhhc093blByb3BlcnR5IiwiY2xhc3NOYW1lcyIsImNsYXNzZXMiLCJpIiwiYXJndW1lbnRzIiwibGVuZ3RoIiwiYXJnIiwiYXJnVHlwZSIsInB1c2giLCJBcnJheSIsImlzQXJyYXkiLCJpbm5lciIsImFwcGx5IiwidG9TdHJpbmciLCJPYmplY3QiLCJwcm90b3R5cGUiLCJpbmNsdWRlcyIsImtleSIsImNhbGwiLCJqb2luIiwibW9kdWxlIiwiZXhwb3J0cyIsImRlZmF1bHQiLCJ3aW5kb3ciLCJfZXh0ZW5kcyIsImFzc2lnbiIsImJpbmQiLCJ0YXJnZXQiLCJzb3VyY2UiLCJfb2JqZWN0V2l0aG91dFByb3BlcnRpZXNMb29zZSIsImV4Y2x1ZGVkIiwic291cmNlS2V5cyIsImtleXMiLCJpbmRleE9mIiwiZGVmYXVsdEtleSIsImNoYXJBdCIsInRvVXBwZXJDYXNlIiwic3Vic3RyIiwiX3RvUHJvcGVydHlLZXkiLCJfdG9QcmltaXRpdmUiLCJTdHJpbmciLCJpbnB1dCIsImhpbnQiLCJwcmltIiwiU3ltYm9sIiwidG9QcmltaXRpdmUiLCJ1bmRlZmluZWQiLCJyZXMiLCJUeXBlRXJyb3IiLCJOdW1iZXIiLCJ1c2VVbmNvbnRyb2xsZWRQcm9wIiwicHJvcFZhbHVlIiwiZGVmYXVsdFZhbHVlIiwiaGFuZGxlciIsIndhc1Byb3BSZWYiLCJ1c2VSZWYiLCJfdXNlU3RhdGUiLCJ1c2VTdGF0ZSIsInN0YXRlVmFsdWUiLCJzZXRTdGF0ZSIsImlzUHJvcCIsIndhc1Byb3AiLCJjdXJyZW50IiwidXNlQ2FsbGJhY2siLCJ2YWx1ZSIsIl9sZW4iLCJhcmdzIiwiX2tleSIsImNvbmNhdCIsInVzZVVuY29udHJvbGxlZCIsInByb3BzIiwiY29uZmlnIiwicmVkdWNlIiwicmVzdWx0IiwiZmllbGROYW1lIiwiX2V4dGVuZHMyIiwiX3JlZiIsIlV0aWxzIiwicHJvcHNWYWx1ZSIsInJlc3QiLCJtYXAiLCJoYW5kbGVyTmFtZSIsIl91c2VVbmNvbnRyb2xsZWRQcm9wIiwiX3NldFByb3RvdHlwZU9mIiwibyIsInAiLCJzZXRQcm90b3R5cGVPZiIsIl9fcHJvdG9fXyIsIl9pbmhlcml0c0xvb3NlIiwic3ViQ2xhc3MiLCJzdXBlckNsYXNzIiwiY3JlYXRlIiwiY29uc3RydWN0b3IiLCJERUZBVUxUX0JSRUFLUE9JTlRTIiwiREVGQVVMVF9NSU5fQlJFQUtQT0lOVCIsIlRoZW1lQ29udGV4dCIsIlJlYWN0IiwiY3JlYXRlQ29udGV4dCIsInByZWZpeGVzIiwiYnJlYWtwb2ludHMiLCJtaW5CcmVha3BvaW50IiwidXNlQm9vdHN0cmFwUHJlZml4IiwicHJlZml4IiwiZGVmYXVsdFByZWZpeCIsInVzZUNvbnRleHQiLCJvd25lckRvY3VtZW50Iiwibm9kZSIsImRvY3VtZW50Iiwib3duZXJXaW5kb3ciLCJkb2MiLCJkZWZhdWx0VmlldyIsImdldENvbXB1dGVkU3R5bGUiLCJwc3VlZG9FbGVtZW50IiwiclVwcGVyIiwiaHlwaGVuYXRlIiwic3RyaW5nIiwicmVwbGFjZSIsInRvTG93ZXJDYXNlIiwibXNQYXR0ZXJuIiwiaHlwaGVuYXRlU3R5bGVOYW1lIiwic3VwcG9ydGVkVHJhbnNmb3JtcyIsImlzVHJhbnNmb3JtIiwidGVzdCIsInN0eWxlIiwicHJvcGVydHkiLCJjc3MiLCJ0cmFuc2Zvcm1zIiwiZ2V0UHJvcGVydHlWYWx1ZSIsImZvckVhY2giLCJyZW1vdmVQcm9wZXJ0eSIsImNzc1RleHQiLCJoYXNTeW1ib2wiLCJmb3IiLCJSRUFDVF9FTEVNRU5UX1RZUEUiLCJSRUFDVF9QT1JUQUxfVFlQRSIsIlJFQUNUX0ZSQUdNRU5UX1RZUEUiLCJSRUFDVF9TVFJJQ1RfTU9ERV9UWVBFIiwiUkVBQ1RfUFJPRklMRVJfVFlQRSIsIlJFQUNUX1BST1ZJREVSX1RZUEUiLCJSRUFDVF9DT05URVhUX1RZUEUiLCJSRUFDVF9BU1lOQ19NT0RFX1RZUEUiLCJSRUFDVF9DT05DVVJSRU5UX01PREVfVFlQRSIsIlJFQUNUX0ZPUldBUkRfUkVGX1RZUEUiLCJSRUFDVF9TVVNQRU5TRV9UWVBFIiwiUkVBQ1RfU1VTUEVOU0VfTElTVF9UWVBFIiwiUkVBQ1RfTUVNT19UWVBFIiwiUkVBQ1RfTEFaWV9UWVBFIiwiUkVBQ1RfQkxPQ0tfVFlQRSIsIlJFQUNUX0ZVTkRBTUVOVEFMX1RZUEUiLCJSRUFDVF9SRVNQT05ERVJfVFlQRSIsIlJFQUNUX1NDT1BFX1RZUEUiLCJpc1ZhbGlkRWxlbWVudFR5cGUiLCJ0eXBlIiwiJCR0eXBlb2YiLCJ0eXBlT2YiLCJvYmplY3QiLCIkJHR5cGVvZlR5cGUiLCJBc3luY01vZGUiLCJDb25jdXJyZW50TW9kZSIsIkNvbnRleHRDb25zdW1lciIsIkNvbnRleHRQcm92aWRlciIsIkVsZW1lbnQiLCJGb3J3YXJkUmVmIiwiRnJhZ21lbnQiLCJMYXp5IiwiTWVtbyIsIlBvcnRhbCIsIlByb2ZpbGVyIiwiU3RyaWN0TW9kZSIsIlN1c3BlbnNlIiwiaGFzV2FybmVkQWJvdXREZXByZWNhdGVkSXNBc3luY01vZGUiLCJpc0FzeW5jTW9kZSIsImNvbnNvbGUiLCJpc0NvbmN1cnJlbnRNb2RlIiwiaXNDb250ZXh0Q29uc3VtZXIiLCJpc0NvbnRleHRQcm92aWRlciIsImlzRWxlbWVudCIsImlzRm9yd2FyZFJlZiIsImlzRnJhZ21lbnQiLCJpc0xhenkiLCJpc01lbW8iLCJpc1BvcnRhbCIsImlzUHJvZmlsZXIiLCJpc1N0cmljdE1vZGUiLCJpc1N1c3BlbnNlIiwicmVxdWlyZSIsImdldE93blByb3BlcnR5U3ltYm9scyIsInByb3BJc0VudW1lcmFibGUiLCJwcm9wZXJ0eUlzRW51bWVyYWJsZSIsInRvT2JqZWN0IiwidmFsIiwic2hvdWxkVXNlTmF0aXZlIiwidGVzdDEiLCJnZXRPd25Qcm9wZXJ0eU5hbWVzIiwidGVzdDIiLCJmcm9tQ2hhckNvZGUiLCJvcmRlcjIiLCJuIiwidGVzdDMiLCJzcGxpdCIsImxldHRlciIsImVyciIsImZyb20iLCJ0byIsInN5bWJvbHMiLCJzIiwiUmVhY3RQcm9wVHlwZXNTZWNyZXQiLCJGdW5jdGlvbiIsInByaW50V2FybmluZyIsImxvZ2dlZFR5cGVGYWlsdXJlcyIsImhhcyIsInRleHQiLCJtZXNzYWdlIiwiZXJyb3IiLCJFcnJvciIsIngiLCJjaGVja1Byb3BUeXBlcyIsInR5cGVTcGVjcyIsInZhbHVlcyIsImxvY2F0aW9uIiwiY29tcG9uZW50TmFtZSIsImdldFN0YWNrIiwidHlwZVNwZWNOYW1lIiwibmFtZSIsImV4Iiwic3RhY2siLCJyZXNldFdhcm5pbmdDYWNoZSIsIlJlYWN0SXMiLCJlbXB0eUZ1bmN0aW9uVGhhdFJldHVybnNOdWxsIiwiaXNWYWxpZEVsZW1lbnQiLCJ0aHJvd09uRGlyZWN0QWNjZXNzIiwiSVRFUkFUT1JfU1lNQk9MIiwiaXRlcmF0b3IiLCJGQVVYX0lURVJBVE9SX1NZTUJPTCIsImdldEl0ZXJhdG9yRm4iLCJtYXliZUl0ZXJhYmxlIiwiaXRlcmF0b3JGbiIsIkFOT05ZTU9VUyIsIlJlYWN0UHJvcFR5cGVzIiwiYXJyYXkiLCJjcmVhdGVQcmltaXRpdmVUeXBlQ2hlY2tlciIsImJpZ2ludCIsImJvb2wiLCJmdW5jIiwibnVtYmVyIiwic3ltYm9sIiwiYW55IiwiY3JlYXRlQW55VHlwZUNoZWNrZXIiLCJhcnJheU9mIiwiY3JlYXRlQXJyYXlPZlR5cGVDaGVja2VyIiwiZWxlbWVudCIsImNyZWF0ZUVsZW1lbnRUeXBlQ2hlY2tlciIsImVsZW1lbnRUeXBlIiwiY3JlYXRlRWxlbWVudFR5cGVUeXBlQ2hlY2tlciIsImluc3RhbmNlT2YiLCJjcmVhdGVJbnN0YW5jZVR5cGVDaGVja2VyIiwiY3JlYXRlTm9kZUNoZWNrZXIiLCJvYmplY3RPZiIsImNyZWF0ZU9iamVjdE9mVHlwZUNoZWNrZXIiLCJvbmVPZiIsImNyZWF0ZUVudW1UeXBlQ2hlY2tlciIsIm9uZU9mVHlwZSIsImNyZWF0ZVVuaW9uVHlwZUNoZWNrZXIiLCJzaGFwZSIsImNyZWF0ZVNoYXBlVHlwZUNoZWNrZXIiLCJleGFjdCIsImNyZWF0ZVN0cmljdFNoYXBlVHlwZUNoZWNrZXIiLCJpcyIsInkiLCJQcm9wVHlwZUVycm9yIiwiZGF0YSIsImNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyIiwidmFsaWRhdGUiLCJtYW51YWxQcm9wVHlwZUNhbGxDYWNoZSIsIm1hbnVhbFByb3BUeXBlV2FybmluZ0NvdW50IiwiY2hlY2tUeXBlIiwiaXNSZXF1aXJlZCIsInByb3BOYW1lIiwicHJvcEZ1bGxOYW1lIiwic2VjcmV0IiwiY2FjaGVLZXkiLCJjaGFpbmVkQ2hlY2tUeXBlIiwiZXhwZWN0ZWRUeXBlIiwicHJvcFR5cGUiLCJnZXRQcm9wVHlwZSIsInByZWNpc2VUeXBlIiwiZ2V0UHJlY2lzZVR5cGUiLCJ0eXBlQ2hlY2tlciIsImV4cGVjdGVkQ2xhc3MiLCJleHBlY3RlZENsYXNzTmFtZSIsImFjdHVhbENsYXNzTmFtZSIsImdldENsYXNzTmFtZSIsImV4cGVjdGVkVmFsdWVzIiwidmFsdWVzU3RyaW5nIiwiSlNPTiIsInN0cmluZ2lmeSIsInJlcGxhY2VyIiwiYXJyYXlPZlR5cGVDaGVja2VycyIsInByb2Nlc3MiLCJjaGVja2VyIiwiZ2V0UG9zdGZpeEZvclR5cGVXYXJuaW5nIiwiZXhwZWN0ZWRUeXBlcyIsImNoZWNrZXJSZXN1bHQiLCJleHBlY3RlZFR5cGVzTWVzc2FnZSIsImlzTm9kZSIsImludmFsaWRWYWxpZGF0b3JFcnJvciIsInNoYXBlVHlwZXMiLCJhbGxLZXlzIiwiZXZlcnkiLCJzdGVwIiwiZW50cmllcyIsIm5leHQiLCJkb25lIiwiZW50cnkiLCJpc1N5bWJvbCIsIlJlZ0V4cCIsIkRhdGUiLCJQcm9wVHlwZXMiLCJkaXNhYmxlZCIsInRpbWVvdXRzU2hhcGUiLCJlbnRlciIsImV4aXQiLCJhcHBlYXIiLCJhY3RpdmUiLCJlbnRlckRvbmUiLCJlbnRlckFjdGl2ZSIsImV4aXREb25lIiwiZXhpdEFjdGl2ZSIsImZvcmNlUmVmbG93Iiwic2Nyb2xsVG9wIiwiVU5NT1VOVEVEIiwiRVhJVEVEIiwiRU5URVJJTkciLCJFTlRFUkVEIiwiRVhJVElORyIsIlRyYW5zaXRpb24iLCJfUmVhY3QkQ29tcG9uZW50IiwiY29udGV4dCIsIl90aGlzIiwicGFyZW50R3JvdXAiLCJpc01vdW50aW5nIiwiaW5pdGlhbFN0YXR1cyIsImFwcGVhclN0YXR1cyIsImluIiwidW5tb3VudE9uRXhpdCIsIm1vdW50T25FbnRlciIsInN0YXRlIiwic3RhdHVzIiwibmV4dENhbGxiYWNrIiwiZ2V0RGVyaXZlZFN0YXRlRnJvbVByb3BzIiwicHJldlN0YXRlIiwibmV4dEluIiwiX3Byb3RvIiwiY29tcG9uZW50RGlkTW91bnQiLCJ1cGRhdGVTdGF0dXMiLCJjb21wb25lbnREaWRVcGRhdGUiLCJwcmV2UHJvcHMiLCJuZXh0U3RhdHVzIiwiY29tcG9uZW50V2lsbFVubW91bnQiLCJjYW5jZWxOZXh0Q2FsbGJhY2siLCJnZXRUaW1lb3V0cyIsInRpbWVvdXQiLCJtb3VudGluZyIsIm5vZGVSZWYiLCJSZWFjdERPTSIsImZpbmRET01Ob2RlIiwicGVyZm9ybUVudGVyIiwicGVyZm9ybUV4aXQiLCJfdGhpczIiLCJhcHBlYXJpbmciLCJfcmVmMiIsIm1heWJlTm9kZSIsIm1heWJlQXBwZWFyaW5nIiwidGltZW91dHMiLCJlbnRlclRpbWVvdXQiLCJzYWZlU2V0U3RhdGUiLCJvbkVudGVyZWQiLCJvbkVudGVyIiwib25FbnRlcmluZyIsIm9uVHJhbnNpdGlvbkVuZCIsIl90aGlzMyIsIm9uRXhpdGVkIiwib25FeGl0Iiwib25FeGl0aW5nIiwiY2FuY2VsIiwibmV4dFN0YXRlIiwiY2FsbGJhY2siLCJzZXROZXh0Q2FsbGJhY2siLCJfdGhpczQiLCJldmVudCIsImRvZXNOb3RIYXZlVGltZW91dE9yTGlzdGVuZXIiLCJhZGRFbmRMaXN0ZW5lciIsInNldFRpbWVvdXQiLCJfcmVmMyIsIm1heWJlTmV4dENhbGxiYWNrIiwicmVuZGVyIiwiX3RoaXMkcHJvcHMiLCJjaGlsZHJlbiIsImNoaWxkUHJvcHMiLCJjcmVhdGVFbGVtZW50IiwiVHJhbnNpdGlvbkdyb3VwQ29udGV4dCIsIlByb3ZpZGVyIiwiY2xvbmVFbGVtZW50IiwiQ2hpbGRyZW4iLCJvbmx5IiwiQ29tcG9uZW50IiwiY29udGV4dFR5cGUiLCJwcm9wVHlwZXMiLCJwdCIsIm5vb3AiLCJkZWZhdWx0UHJvcHMiLCJvcHRpb25zU3VwcG9ydGVkIiwib25jZVN1cHBvcnRlZCIsIm9wdGlvbnMiLCJwYXNzaXZlIiwib25jZSIsImNhblVzZURPTSIsImFkZEV2ZW50TGlzdGVuZXIiLCJyZW1vdmVFdmVudExpc3RlbmVyIiwiZSIsImV2ZW50TmFtZSIsImNhcHR1cmUiLCJ3cmFwcGVkSGFuZGxlciIsIl9fb25jZSIsIm9uY2VIYW5kbGVyIiwibGlzdGVuIiwidHJpZ2dlckV2ZW50IiwiYnViYmxlcyIsImNhbmNlbGFibGUiLCJjcmVhdGVFdmVudCIsImluaXRFdmVudCIsImRpc3BhdGNoRXZlbnQiLCJwYXJzZUR1cmF0aW9uIiwic3RyIiwibXVsdCIsInBhcnNlRmxvYXQiLCJlbXVsYXRlVHJhbnNpdGlvbkVuZCIsImR1cmF0aW9uIiwicGFkZGluZyIsImNhbGxlZCIsImhhbmRsZSIsInJlbW92ZSIsImNsZWFyVGltZW91dCIsInRyYW5zaXRpb25FbmQiLCJyZW1vdmVFbXVsYXRlIiwidHJhbnNpdGlvbkVuZExpc3RlbmVyIiwiZGVsYXkiLCJjcmVhdGVDaGFpbmVkRnVuY3Rpb24iLCJmdW5jcyIsImZpbHRlciIsImYiLCJhY2MiLCJjaGFpbmVkRnVuY3Rpb24iLCJ0cmlnZ2VyQnJvd3NlclJlZmxvdyIsIm9mZnNldEhlaWdodCIsInRvRm5SZWYiLCJyZWYiLCJtZXJnZVJlZnMiLCJyZWZBIiwicmVmQiIsImEiLCJiIiwidXNlTWVyZ2VkUmVmcyIsInVzZU1lbW8iLCJzYWZlRmluZERPTU5vZGUiLCJjb21wb25lbnRPckVsZW1lbnQiLCJUcmFuc2l0aW9uV3JhcHBlciIsImZvcndhcmRSZWYiLCJjaGlsZFJlZiIsIm1lcmdlZFJlZiIsImF0dGFjaFJlZiIsInIiLCJub3JtYWxpemUiLCJwYXJhbSIsImhhbmRsZUVudGVyIiwiaGFuZGxlRW50ZXJpbmciLCJoYW5kbGVFbnRlcmVkIiwiaGFuZGxlRXhpdCIsImhhbmRsZUV4aXRpbmciLCJoYW5kbGVFeGl0ZWQiLCJoYW5kbGVBZGRFbmRMaXN0ZW5lciIsIl9qc3giLCJpbm5lclByb3BzIiwiTUFSR0lOUyIsImhlaWdodCIsIndpZHRoIiwiZ2V0RGVmYXVsdERpbWVuc2lvblZhbHVlIiwiZGltZW5zaW9uIiwiZWxlbSIsIm9mZnNldCIsInNsaWNlIiwibWFyZ2lucyIsInBhcnNlSW50IiwiY29sbGFwc2VTdHlsZXMiLCJnZXREaW1lbnNpb25WYWx1ZSIsIkNvbGxhcHNlIiwiY2xhc3NOYW1lIiwiY29tcHV0ZWREaW1lbnNpb24iLCJzY3JvbGwiLCJyb2xlIiwiaXNBY2NvcmRpb25JdGVtU2VsZWN0ZWQiLCJhY3RpdmVFdmVudEtleSIsImV2ZW50S2V5IiwiZGlzcGxheU5hbWUiLCJBY2NvcmRpb25Db2xsYXBzZSIsImFzIiwiYnNQcmVmaXgiLCJBY2NvcmRpb25Db250ZXh0IiwiQWNjb3JkaW9uQm9keSIsIkFjY29yZGlvbkl0ZW1Db250ZXh0IiwidXNlQWNjb3JkaW9uQnV0dG9uIiwib25DbGljayIsIm9uU2VsZWN0IiwiYWx3YXlzT3BlbiIsImV2ZW50S2V5UGFzc2VkIiwiayIsIkFjY29yZGlvbkJ1dHRvbiIsImFjY29yZGlvbk9uQ2xpY2siLCJBY2NvcmRpb25IZWFkZXIiLCJBY2NvcmRpb25JdGVtIiwiY29udGV4dFZhbHVlIiwiQWNjb3JkaW9uIiwiYWN0aXZlS2V5IiwiZmx1c2giLCJjb250cm9sbGVkUHJvcHMiLCJCdXR0b24iLCJJdGVtIiwiSGVhZGVyIiwiQm9keSJdLCJtYXBwaW5ncyI6Ijs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Q0FLQTs7Q0FFQyxDQUFBLENBQVksWUFBQTs7Q0FHWixHQUFBLElBQUlBLE1BQU0sR0FBRyxFQUFFLENBQUNDLGNBQWMsQ0FBQTtJQUc5QixTQUFTQyxVQUFVLEdBQUc7TUFDckIsSUFBSUMsT0FBTyxHQUFHLEVBQUUsQ0FBQTtDQUVoQixLQUFBLEtBQUssSUFBSUMsQ0FBQyxHQUFHLENBQUMsRUFBRUEsQ0FBQyxHQUFHQyxTQUFTLENBQUNDLE1BQU0sRUFBRUYsQ0FBQyxFQUFFLEVBQUU7Q0FDMUMsT0FBQSxJQUFJRyxHQUFHLEdBQUdGLFNBQVMsQ0FBQ0QsQ0FBQyxDQUFDLENBQUE7UUFDdEIsSUFBSSxDQUFDRyxHQUFHLEVBQUUsU0FBQTtRQUVWLElBQUlDLE9BQU8sR0FBRyxPQUFPRCxHQUFHLENBQUE7UUFFeEIsSUFBSUMsT0FBTyxLQUFLLFFBQVEsSUFBSUEsT0FBTyxLQUFLLFFBQVEsRUFBRTtDQUNqREwsU0FBQUEsT0FBTyxDQUFDTSxJQUFJLENBQUNGLEdBQUcsQ0FBQyxDQUFBO1NBQ2pCLE1BQU0sSUFBSUcsS0FBSyxDQUFDQyxPQUFPLENBQUNKLEdBQUcsQ0FBQyxFQUFFO1VBQzlCLElBQUlBLEdBQUcsQ0FBQ0QsTUFBTSxFQUFFO1lBQ2YsSUFBSU0sS0FBSyxHQUFHVixVQUFVLENBQUNXLEtBQUssQ0FBQyxJQUFJLEVBQUVOLEdBQUcsQ0FBQyxDQUFBO1lBQ3ZDLElBQUlLLEtBQUssRUFBRTtDQUNWVCxhQUFBQSxPQUFPLENBQUNNLElBQUksQ0FBQ0csS0FBSyxDQUFDLENBQUE7YUFDcEI7V0FDRDtDQUNELFFBQUMsTUFBTSxJQUFJSixPQUFPLEtBQUssUUFBUSxFQUFFO1VBQ2hDLElBQUlELEdBQUcsQ0FBQ08sUUFBUSxLQUFL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
