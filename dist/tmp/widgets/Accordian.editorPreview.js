'use strict';

Object.defineProperty(exports, '__esModule', { value: true });

var react = require('react');

function getDefaultExportFromNamespaceIfNotNamed (n) {
	return n && Object.prototype.hasOwnProperty.call(n, 'default') && Object.keys(n).length === 1 ? n['default'] : n;
}

function styleInject(css, ref) {
  if (ref === void 0) ref = {};
  var insertAt = ref.insertAt;
  if (!css || typeof document === 'undefined') {
    return;
  }
  var head = document.head || document.getElementsByTagName('head')[0];
  var style = document.createElement('style');
  style.type = 'text/css';
  if (insertAt === 'top') {
    if (head.firstChild) {
      head.insertBefore(style, head.firstChild);
    } else {
      head.appendChild(style);
    }
  } else {
    head.appendChild(style);
  }
  if (style.styleSheet) {
    style.styleSheet.cssText = css;
  } else {
    style.appendChild(document.createTextNode(css));
  }
}

var css_248z = "/*\nPlace your custom CSS here\n*/\n\n.AccordianHeader{\n    width: 100%;\n    background-color: white;\n    border-radius: 10px;\n    height: 50px;\n    border: 1px solid gray;\n    text-align: left;\n    padding: 0 0 0 25px;\n}\n\n.accordion-header > button{\n    border: none;\n    background-color: white;\n    margin: 8px 0 0 0;\n    width: 100%;\n    height: 30px;\n    text-align: left;\n}\n/*# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIkFjY29yZGlhbi5jc3MiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUE7O0NBRUM7O0FBRUQ7SUFDSSxXQUFXO0lBQ1gsdUJBQXVCO0lBQ3ZCLG1CQUFtQjtJQUNuQixZQUFZO0lBQ1osc0JBQXNCO0lBQ3RCLGdCQUFnQjtJQUNoQixtQkFBbUI7QUFDdkI7O0FBRUE7SUFDSSxZQUFZO0lBQ1osdUJBQXVCO0lBQ3ZCLGlCQUFpQjtJQUNqQixXQUFXO0lBQ1gsWUFBWTtJQUNaLGdCQUFnQjtBQUNwQiIsImZpbGUiOiJBY2NvcmRpYW4uY3NzIiwic291cmNlc0NvbnRlbnQiOlsiLypcblBsYWNlIHlvdXIgY3VzdG9tIENTUyBoZXJlXG4qL1xuXG4uQWNjb3JkaWFuSGVhZGVye1xuICAgIHdpZHRoOiAxMDAlO1xuICAgIGJhY2tncm91bmQtY29sb3I6IHdoaXRlO1xuICAgIGJvcmRlci1yYWRpdXM6IDEwcHg7XG4gICAgaGVpZ2h0OiA1MHB4O1xuICAgIGJvcmRlcjogMXB4IHNvbGlkIGdyYXk7XG4gICAgdGV4dC1hbGlnbjogbGVmdDtcbiAgICBwYWRkaW5nOiAwIDAgMCAyNXB4O1xufVxuXG4uYWNjb3JkaW9uLWhlYWRlciA+IGJ1dHRvbntcbiAgICBib3JkZXI6IG5vbmU7XG4gICAgYmFja2dyb3VuZC1jb2xvcjogd2hpdGU7XG4gICAgbWFyZ2luOiA4cHggMCAwIDA7XG4gICAgd2lkdGg6IDEwMCU7XG4gICAgaGVpZ2h0OiAzMHB4O1xuICAgIHRleHQtYWxpZ246IGxlZnQ7XG59Il19 */";
var stylesheet="/*\nPlace your custom CSS here\n*/\n\n.AccordianHeader{\n    width: 100%;\n    background-color: white;\n    border-radius: 10px;\n    height: 50px;\n    border: 1px solid gray;\n    text-align: left;\n    padding: 0 0 0 25px;\n}\n\n.accordion-header > button{\n    border: none;\n    background-color: white;\n    margin: 8px 0 0 0;\n    width: 100%;\n    height: 30px;\n    text-align: left;\n}\n/*# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIkFjY29yZGlhbi5jc3MiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUE7O0NBRUM7O0FBRUQ7SUFDSSxXQUFXO0lBQ1gsdUJBQXVCO0lBQ3ZCLG1CQUFtQjtJQUNuQixZQUFZO0lBQ1osc0JBQXNCO0lBQ3RCLGdCQUFnQjtJQUNoQixtQkFBbUI7QUFDdkI7O0FBRUE7SUFDSSxZQUFZO0lBQ1osdUJBQXVCO0lBQ3ZCLGlCQUFpQjtJQUNqQixXQUFXO0lBQ1gsWUFBWTtJQUNaLGdCQUFnQjtBQUNwQiIsImZpbGUiOiJBY2NvcmRpYW4uY3NzIiwic291cmNlc0NvbnRlbnQiOlsiLypcblBsYWNlIHlvdXIgY3VzdG9tIENTUyBoZXJlXG4qL1xuXG4uQWNjb3JkaWFuSGVhZGVye1xuICAgIHdpZHRoOiAxMDAlO1xuICAgIGJhY2tncm91bmQtY29sb3I6IHdoaXRlO1xuICAgIGJvcmRlci1yYWRpdXM6IDEwcHg7XG4gICAgaGVpZ2h0OiA1MHB4O1xuICAgIGJvcmRlcjogMXB4IHNvbGlkIGdyYXk7XG4gICAgdGV4dC1hbGlnbjogbGVmdDtcbiAgICBwYWRkaW5nOiAwIDAgMCAyNXB4O1xufVxuXG4uYWNjb3JkaW9uLWhlYWRlciA+IGJ1dHRvbntcbiAgICBib3JkZXI6IG5vbmU7XG4gICAgYmFja2dyb3VuZC1jb2xvcjogd2hpdGU7XG4gICAgbWFyZ2luOiA4cHggMCAwIDA7XG4gICAgd2lkdGg6IDEwMCU7XG4gICAgaGVpZ2h0OiAzMHB4O1xuICAgIHRleHQtYWxpZ246IGxlZnQ7XG59Il19 */";
styleInject(css_248z);

var Accordian = /*#__PURE__*/Object.freeze({
	__proto__: null,
	'default': css_248z,
	stylesheet: stylesheet
});

var require$$0 = /*@__PURE__*/getDefaultExportFromNamespaceIfNotNamed(Accordian);

class preview extends react.Component {
    render() {
        return react.createElement("div", null);
    }
}
function getPreviewCss() {
    return require$$0;
}

exports.getPreviewCss = getPreviewCss;
exports.preview = preview;
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiQWNjb3JkaWFuLmVkaXRvclByZXZpZXcuanMiLCJzb3VyY2VzIjpbIi4uLy4uLy4uL25vZGVfbW9kdWxlcy9zdHlsZS1pbmplY3QvZGlzdC9zdHlsZS1pbmplY3QuZXMuanMiLCIuLi8uLi8uLi9zcmMvQWNjb3JkaWFuLmVkaXRvclByZXZpZXcudHN4Il0sInNvdXJjZXNDb250ZW50IjpbImZ1bmN0aW9uIHN0eWxlSW5qZWN0KGNzcywgcmVmKSB7XG4gIGlmICggcmVmID09PSB2b2lkIDAgKSByZWYgPSB7fTtcbiAgdmFyIGluc2VydEF0ID0gcmVmLmluc2VydEF0O1xuXG4gIGlmICghY3NzIHx8IHR5cGVvZiBkb2N1bWVudCA9PT0gJ3VuZGVmaW5lZCcpIHsgcmV0dXJuOyB9XG5cbiAgdmFyIGhlYWQgPSBkb2N1bWVudC5oZWFkIHx8IGRvY3VtZW50LmdldEVsZW1lbnRzQnlUYWdOYW1lKCdoZWFkJylbMF07XG4gIHZhciBzdHlsZSA9IGRvY3VtZW50LmNyZWF0ZUVsZW1lbnQoJ3N0eWxlJyk7XG4gIHN0eWxlLnR5cGUgPSAndGV4dC9jc3MnO1xuXG4gIGlmIChpbnNlcnRBdCA9PT0gJ3RvcCcpIHtcbiAgICBpZiAoaGVhZC5maXJzdENoaWxkKSB7XG4gICAgICBoZWFkLmluc2VydEJlZm9yZShzdHlsZSwgaGVhZC5maXJzdENoaWxkKTtcbiAgICB9IGVsc2Uge1xuICAgICAgaGVhZC5hcHBlbmRDaGlsZChzdHlsZSk7XG4gICAgfVxuICB9IGVsc2Uge1xuICAgIGhlYWQuYXBwZW5kQ2hpbGQoc3R5bGUpO1xuICB9XG5cbiAgaWYgKHN0eWxlLnN0eWxlU2hlZXQpIHtcbiAgICBzdHlsZS5zdHlsZVNoZWV0LmNzc1RleHQgPSBjc3M7XG4gIH0gZWxzZSB7XG4gICAgc3R5bGUuYXBwZW5kQ2hpbGQoZG9jdW1lbnQuY3JlYXRlVGV4dE5vZGUoY3NzKSk7XG4gIH1cbn1cblxuZXhwb3J0IGRlZmF1bHQgc3R5bGVJbmplY3Q7XG4iLCJpbXBvcnQgeyBDb21wb25lbnQsIFJlYWN0Tm9kZSwgY3JlYXRlRWxlbWVudCB9IGZyb20gXCJyZWFjdFwiO1xuaW1wb3J0IHsgQWNjb3JkaWFuUHJldmlld1Byb3BzIH0gZnJvbSBcIi4uL3R5cGluZ3MvQWNjb3JkaWFuUHJvcHNcIjtcblxuZXhwb3J0IGNsYXNzIHByZXZpZXcgZXh0ZW5kcyBDb21wb25lbnQ8QWNjb3JkaWFuUHJldmlld1Byb3BzPiB7XG4gICAgcmVuZGVyKCk6IFJlYWN0Tm9kZSB7XG4gICAgICAgIHJldHVybiA8ZGl2ID48L2Rpdj47XG4gICAgfVxufVxuXG5leHBvcnQgZnVuY3Rpb24gZ2V0UHJldmlld0NzcygpOiBzdHJpbmcge1xuICAgIHJldHVybiByZXF1aXJlKFwiLi91aS9BY2NvcmRpYW4uY3NzXCIpO1xufVxuIl0sIm5hbWVzIjpbInN0eWxlSW5qZWN0IiwiY3NzIiwicmVmIiwiaW5zZXJ0QXQiLCJkb2N1bWVudCIsImhlYWQiLCJnZXRFbGVtZW50c0J5VGFnTmFtZSIsInN0eWxlIiwiY3JlYXRlRWxlbWVudCIsInR5cGUiLCJmaXJzdENoaWxkIiwiaW5zZXJ0QmVmb3JlIiwiYXBwZW5kQ2hpbGQiLCJzdHlsZVNoZWV0IiwiY3NzVGV4dCIsImNyZWF0ZVRleHROb2RlIiwiQ29tcG9uZW50Il0sIm1hcHBpbmdzIjoiOzs7Ozs7Ozs7O0FBQUEsU0FBU0EsV0FBVyxDQUFDQyxHQUFHLEVBQUVDLEdBQUcsRUFBRTtFQUM3QixJQUFLQSxHQUFHLEtBQUssS0FBSyxDQUFDLEVBQUdBLEdBQUcsR0FBRyxFQUFFLENBQUE7QUFDOUIsRUFBQSxJQUFJQyxRQUFRLEdBQUdELEdBQUcsQ0FBQ0MsUUFBUSxDQUFBO0FBRTNCLEVBQUEsSUFBSSxDQUFDRixHQUFHLElBQUksT0FBT0csUUFBUSxLQUFLLFdBQVcsRUFBRTtBQUFFLElBQUEsT0FBQTtBQUFRLEdBQUE7QUFFdkQsRUFBQSxJQUFJQyxJQUFJLEdBQUdELFFBQVEsQ0FBQ0MsSUFBSSxJQUFJRCxRQUFRLENBQUNFLG9CQUFvQixDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFBO0FBQ3BFLEVBQUEsSUFBSUMsS0FBSyxHQUFHSCxRQUFRLENBQUNJLGFBQWEsQ0FBQyxPQUFPLENBQUMsQ0FBQTtFQUMzQ0QsS0FBSyxDQUFDRSxJQUFJLEdBQUcsVUFBVSxDQUFBO0VBRXZCLElBQUlOLFFBQVEsS0FBSyxLQUFLLEVBQUU7SUFDdEIsSUFBSUUsSUFBSSxDQUFDSyxVQUFVLEVBQUU7TUFDbkJMLElBQUksQ0FBQ00sWUFBWSxDQUFDSixLQUFLLEVBQUVGLElBQUksQ0FBQ0ssVUFBVSxDQUFDLENBQUE7QUFDM0MsS0FBQyxNQUFNO0FBQ0xMLE1BQUFBLElBQUksQ0FBQ08sV0FBVyxDQUFDTCxLQUFLLENBQUMsQ0FBQTtBQUN6QixLQUFBO0FBQ0YsR0FBQyxNQUFNO0FBQ0xGLElBQUFBLElBQUksQ0FBQ08sV0FBVyxDQUFDTCxLQUFLLENBQUMsQ0FBQTtBQUN6QixHQUFBO0VBRUEsSUFBSUEsS0FBSyxDQUFDTSxVQUFVLEVBQUU7QUFDcEJOLElBQUFBLEtBQUssQ0FBQ00sVUFBVSxDQUFDQyxPQUFPLEdBQUdiLEdBQUcsQ0FBQTtBQUNoQyxHQUFDLE1BQU07SUFDTE0sS0FBSyxDQUFDSyxXQUFXLENBQUNSLFFBQVEsQ0FBQ1csY0FBYyxDQUFDZCxHQUFHLENBQUMsQ0FBQyxDQUFBO0FBQ2pELEdBQUE7QUFDRjs7Ozs7Ozs7Ozs7Ozs7QUN0Qk0sTUFBTyxPQUFRLFNBQVFlLGVBQWdDLENBQUE7SUFDekQsTUFBTSxHQUFBO0FBQ0YsUUFBQSxPQUFPUixnQ0FBWSxDQUFDO0tBQ3ZCO0FBQ0osQ0FBQTtTQUVlLGFBQWEsR0FBQTtBQUN6QixJQUFBLE9BQU8sVUFBNkIsQ0FBQztBQUN6Qzs7Ozs7In0=
