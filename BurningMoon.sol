/*
 Burning Moon

!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
 Please Read carefully before doing a Rugscreen 
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
 BurningMoon differentiates between Buys/Sells/Transfers
 to apply different taxes/Limits to the transfer.
 This can be abused to disable sells to create a Honeypot.

Burning Moon also locks you from selling/transfering for 2 hours after each Transfer.

Rugscreens will rightfully warn you about that.

Also, BurningMoon includes a Liquidity lock function that can release the liquidity once the Lock
time is over.

Please DYOR and try to understand what the code actually does.
I tried to comment it well so everyone can understand it.
The Contract starts at Line 840.
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

BurningMoon is a Hyper Deflationary Token.
There is an initial supply of 100.000.000 Token,
the goal is to reduce the supply to less than 21.000.000 Token(Bitcoin max. Supply)

Each transaction 3 things Happen:

Burn: 
Burning Moon Burns clean and without residue.
Tokens will not just land in a burn-wallet (or worse, Vitaliks Wallet),
they will be completely removed from existance.

Auto Liquidity: 
A Massive Burn requires enough liquidity to control the Burn.
That way everyone can sell their BurningMoon without worrying about price impact.

Marketing Tax: 

Marketing:
    The Marketing Tax flows to a Multisig wallet converted to BNB.
    We want large parts of the Marketing tax to flow back to the holders.
    A small percentage will be used to pay the team. 
    That way we avoid to have team tokens. 

Donations:
    Each week the whole marketing wallet automatically gets donated to a charity wallet.
    Our goal is to burn the Moon, but keep the Earth cool.



Whale Protection:
    Any Buy/Transfer where the recipient would recieve more than 0.5% of the supply(before taxes) will be declined.

Dump Protection:
    Any Sell over 0.05% of the total supply gets declined. 
    Sellers get locked from selling/transfering for 2 hours after selling.

*/


// SPDX-License-Identifier: MIT

pragma solidity ^0.7.4;

interface IBEP20 {
  function totalSupply() external view returns (uint256);
  function decimals() external view returns (uint8);
  function symbol() external view returns (string memory);
  function name() external view returns (string memory);
  function getOwner() external view returns (address);
  function balanceOf(address account) external view returns (uint256);
  function transfer(address recipient, uint256 amount) external returns (bool);
  function allowance(address _owner, address spender) external view returns (uint256);
  function approve(address spender, uint256 amount) external returns (bool);
  function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);
  event Transfer(address indexed from, address indexed to, uint256 value);
  event Approval(address indexed owner, address indexed spender, uint256 value);
}




pragma solidity ^0.7.4;

interface IPancakeERC20 {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);
    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);
    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);
    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;
}

interface IPancakeFactory {
    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    function feeTo() external view returns (address);
    function feeToSetter() external view returns (address);
    function getPair(address tokenA, address tokenB) external view returns (address pair);
    function allPairs(uint) external view returns (address pair);
    function allPairsLength() external view returns (uint);
    function createPair(address tokenA, address tokenB) external returns (address pair);
    function setFeeTo(address) external;
    function setFeeToSetter(address) external;
}

interface IPancakeRouter01 {
    function addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB, uint liquidity);
    function addLiquidityETH(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external payable returns (uint amountToken, uint amountETH, uint liquidity);
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETH(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountToken, uint amountETH);
    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETHWithPermit(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountToken, uint amountETH);
    function swapExactTokensForTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapTokensForExactTokens(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapExactETHForTokens(uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);
    function swapTokensForExactETH(uint amountOut, uint amountInMax, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapExactTokensForETH(uint amountIn, uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapETHForExactTokens(uint amountOut, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);

    function factory() external pure returns (address);
    function WETH() external pure returns (address);
    function quote(uint amountA, uint reserveA, uint reserveB) external pure returns (uint amountB);
    function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) external pure returns (uint amountOut);
    function getAmountIn(uint amountOut, uint reserveIn, uint reserveOut) external pure returns (uint amountIn);
    function getAmountsOut(uint amountIn, address[] calldata path) external view returns (uint[] memory amounts);
    function getAmountsIn(uint amountOut, address[] calldata path) external view returns (uint[] memory amounts);
}

interface IPancakeRouter02 is IPancakeRouter01 {
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountETH);
    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountETH);
    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable;
    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
}






pragma solidity ^0.7.4;

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view returns (address) {
        return msg.sender;
    }

    function _msgData() internal view returns (bytes calldata) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}





pragma solidity ^0.7.4;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}


























pragma solidity ^0.7.4;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: value }(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data, string memory errorMessage) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(bool success, bytes memory returndata, string memory errorMessage) private pure returns(bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}










pragma solidity ^0.7.3;

/**
 * @dev Library for managing
 * https://en.wikipedia.org/wiki/Set_(abstract_data_type)[sets] of primitive
 * types.
 *
 * Sets have the following properties:
 *
 * - Elements are added, removed, and checked for existence in constant time
 * (O(1)).
 * - Elements are enumerated in O(n). No guarantees are made on the ordering.
 *
 * ```
 * contract Example {
 *     // Add the library methods
 *     using EnumerableSet for EnumerableSet.AddressSet;
 *
 *     // Declare a set state variable
 *     EnumerableSet.AddressSet private mySet;
 * }
 * ```
 *
 * As of v3.3.0, sets of type `bytes32` (`Bytes32Set`), `address` (`AddressSet`)
 * and `uint256` (`UintSet`) are supported.
 */
library EnumerableSet {
    // To implement this library for multiple types with as little code
    // repetition as possible, we write it in terms of a generic Set type with
    // bytes32 values.
    // The Set implementation uses private functions, and user-facing
    // implementations (such as AddressSet) are just wrappers around the
    // underlying Set.
    // This means that we can only create new EnumerableSets for types that fit
    // in bytes32.

    struct Set {
        // Storage of set values
        bytes32[] _values;

        // Position of the value in the `values` array, plus 1 because index 0
        // means a value is not in the set.
        mapping (bytes32 => uint256) _indexes;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function _add(Set storage set, bytes32 value) private returns (bool) {
        if (!_contains(set, value)) {
            set._values.push(value);
            // The value is stored at length-1, but we add 1 to all indexes
            // and use 0 as a sentinel value
            set._indexes[value] = set._values.length;
            return true;
        } else {
            return false;
        }
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function _remove(Set storage set, bytes32 value) private returns (bool) {
        // We read and store the value's index to prevent multiple reads from the same storage slot
        uint256 valueIndex = set._indexes[value];

        if (valueIndex != 0) { // Equivalent to contains(set, value)
            // To delete an element from the _values array in O(1), we swap the element to delete with the last one in
            // the array, and then remove the last element (sometimes called as 'swap and pop').
            // This modifies the order of the array, as noted in {at}.

            uint256 toDeleteIndex = valueIndex - 1;
            uint256 lastIndex = set._values.length - 1;

            // When the value to delete is the last one, the swap operation is unnecessary. However, since this occurs
            // so rarely, we still do the swap anyway to avoid the gas cost of adding an 'if' statement.

            bytes32 lastvalue = set._values[lastIndex];

            // Move the last value to the index where the value to delete is
            set._values[toDeleteIndex] = lastvalue;
            // Update the index for the moved value
            set._indexes[lastvalue] = valueIndex; // Replace lastvalue's index to valueIndex

            // Delete the slot where the moved value was stored
            set._values.pop();

            // Delete the index for the deleted slot
            delete set._indexes[value];

            return true;
        } else {
            return false;
        }
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function _contains(Set storage set, bytes32 value) private view returns (bool) {
        return set._indexes[value] != 0;
    }

    /**
     * @dev Returns the number of values on the set. O(1).
     */
    function _length(Set storage set) private view returns (uint256) {
        return set._values.length;
    }

   /**
    * @dev Returns the value stored at position `index` in the set. O(1).
    *
    * Note that there are no guarantees on the ordering of values inside the
    * array, and it may change when more values are added or removed.
    *
    * Requirements:
    *
    * - `index` must be strictly less than {length}.
    */
    function _at(Set storage set, uint256 index) private view returns (bytes32) {
        require(set._values.length > index, "EnumerableSet: index out of bounds");
        return set._values[index];
    }

    // Bytes32Set

    struct Bytes32Set {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _add(set._inner, value);
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _remove(set._inner, value);
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(Bytes32Set storage set, bytes32 value) internal view returns (bool) {
        return _contains(set._inner, value);
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(Bytes32Set storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

   /**
    * @dev Returns the value stored at position `index` in the set. O(1).
    *
    * Note that there are no guarantees on the ordering of values inside the
    * array, and it may change when more values are added or removed.
    *
    * Requirements:
    *
    * - `index` must be strictly less than {length}.
    */
    function at(Bytes32Set storage set, uint256 index) internal view returns (bytes32) {
        return _at(set._inner, index);
    }

    // AddressSet

    struct AddressSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(AddressSet storage set, address value) internal returns (bool) {
        return _add(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(AddressSet storage set, address value) internal returns (bool) {
        return _remove(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(AddressSet storage set, address value) internal view returns (bool) {
        return _contains(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(AddressSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

   /**
    * @dev Returns the value stored at position `index` in the set. O(1).
    *
    * Note that there are no guarantees on the ordering of values inside the
    * array, and it may change when more values are added or removed.
    *
    * Requirements:
    *
    * - `index` must be strictly less than {length}.
    */
    function at(AddressSet storage set, uint256 index) internal view returns (address) {
        return address(uint160(uint256(_at(set._inner, index))));
    }

    // UintSet

    struct UintSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(UintSet storage set, uint256 value) internal returns (bool) {
        return _add(set._inner, bytes32(value));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(UintSet storage set, uint256 value) internal returns (bool) {
        return _remove(set._inner, bytes32(value));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(UintSet storage set, uint256 value) internal view returns (bool) {
        return _contains(set._inner, bytes32(value));
    }

    /**
     * @dev Returns the number of values on the set. O(1).
     */
    function length(UintSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

   /**
    * @dev Returns the value stored at position `index` in the set. O(1).
    *
    * Note that there are no guarantees on the ordering of values inside the
    * array, and it may change when more values are added or removed.
    *
    * Requirements:
    *
    * - `index` must be strictly less than {length}.
    */
    function at(UintSet storage set, uint256 index) internal view returns (uint256) {
        return uint256(_at(set._inner, index));
    }
}










////////////////////////////////////////////////////////////////////////////////////////////////////////
//Burning Moon Contract ////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////
pragma solidity ^0.7.4;
contract Bu2 is IBEP20, Context, Ownable
{
    using Address for address;
    using EnumerableSet for EnumerableSet.AddressSet;
    
    mapping (address => uint256) private _balances;
    mapping (address => mapping (address => uint256)) private _allowances;
    
    mapping (address => uint256) private _sellLock;
    EnumerableSet.AddressSet private _excluded;
    EnumerableSet.AddressSet private _whiteList;
    
    IPancakeRouter02 private _pancakeRouter;
    event SwapAutoLiquidity(uint256 tokens, uint256 bnb);
    event Burn(uint256 amount);

    //Token Info
    string private _name = 'TeBu2';
    string private _symbol = 'Bu2';
    uint8 private _decimals = 9;
    //equals 100.000.000 token
    uint256 private _totalSupply = 100 * 10**6 * 10**9;
    
    //variables that track balanceLimit and sellLimit, get updated based on remaining supply, once contract gets locked or manually 
    uint256 private  _balanceLimit = _totalSupply;
    uint256 private  _sellLimit = _totalSupply;

    //Sellers get locked for 2 hours so they can't dump repeatedly
    //TODO change SellLock
    uint256 private constant _sellLockTime= 2 minutes;
    
    address private _pancakePairAddress;    
    
    
    struct Tax {
        uint burn;
        uint256 liquidity;
        uint256 marketing;
    }
    Tax private _buyTax;
    Tax private _sellTax;
    Tax private _transferTax;
    
    //variables that track the allocation of Taxed Tokens
    uint256 _liquidityBalance;
    uint256 _marketingBalance;


    //Lock for Swap Function.
    //Disables all taxes when token get swapped for Liquidity
    bool private _isSwappingContractToken;
    bool private _isSwappingContractModifier;
    modifier lockTheSwap {
        _isSwappingContractModifier = true;
        _;
        _isSwappingContractModifier = false;
    }
    
    modifier onlyTeam() {
        require(owner() == _msgSender()||_teamWallet==_msgSender(), "Ownable: caller is not the owner");
        _;
    }
    
    

    //Constructor, gets called when contract gets deployed to set up everything
    constructor () {
        _balances[_msgSender()] = _totalSupply;
        emit Transfer(address(0), _msgSender(), _totalSupply);

        // Pancake Router Address
        _pancakeRouter = IPancakeRouter02(0x10ED43C718714eb63d5aA57B78B54704E256024E);
        //Creates a Pancake Pair
        _pancakePairAddress = IPancakeFactory(_pancakeRouter.factory()).createPair(address(this), _pancakeRouter.WETH());

        //Sets the Marketing and donation address to the default address
        
    _donationWallet=_donationWallets[0];
    _marketingWallet=_teamWallet;
    //Set default taxes to 5 Burn, 10 Liquidity, 5 Marketing;
    aSetTaxes(5,10,5,true,true,true);
    }






    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    //Transfer functionality////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    //Main transfer function, all transfers run through this function
    function _transfer(address sender, address recipient, uint256 amount) private
    {
        require(sender != address(0), "Transfer from zero");
        require(recipient != address(0), "Transfer to zero");

        //Manually Excluded adresses are transfering tax and lock free
        bool isExcluded = _excluded.contains(sender) || _excluded.contains(recipient);
        
        //Transactions from and to the contract are always feeless
        bool isContractTransfer=(sender==address(this)|| recipient==address(this));

        //internal Liquidity transfers are feeless
        address pancakeRouter=address(_pancakeRouter);
        bool isLiquidityTransfer = (sender == _pancakePairAddress && recipient == pancakeRouter) 
        || (recipient == _pancakePairAddress && sender == pancakeRouter);

        //owner transfers feeless and can't sell
        bool isOwnerTransfer=(sender==owner()||recipient==owner());

        //differentiate between buy/sell/transfer to apply different taxes/restrictions
        bool isBuy=sender==_pancakePairAddress|| sender == pancakeRouter;
        bool isSell=recipient==_pancakePairAddress|| recipient == pancakeRouter;


        if(isContractTransfer||isLiquidityTransfer||isExcluded
        ||_isSwappingContractToken||_isSwappingContractModifier)
        {
            _feelessTransfer(sender, recipient, amount);
        }
        else if(isOwnerTransfer)
        {
            _ownerTransfer(sender, recipient, amount, isSell);
        }
        else
        { 
            //checks if trading is enabled, otherwise checks whitelist
            if(_tradingEnabled)
            {
                _taxedTransfer(sender,recipient,amount,isBuy,isSell);
            }
            else
            {
                _whiteListTransfer(sender,recipient,amount,isBuy,isSell);
            }
        }
    }
    function _whiteListTransfer(address sender, address recipient, 
    uint256 amount,bool isBuy,bool isSell) private{

                if(block.timestamp<_whiteListTradingTime)
                {
                    require(isBuy,"Only Buys on whitelist");
                    require(_balances[recipient]+amount<100000,"Balance Limit 100.000");
                    _taxedTransfer(sender,recipient,amount,isBuy,isSell);
                    return;
                }
                else
                {
                    require(_whiteListTradingTime>0);                
                    _tradingEnabled=true;
                    _taxedTransfer(sender,recipient,amount,isBuy,isSell);   
                }
    }
    //Owner transfers feeless and can't sell
    function _ownerTransfer(address sender, address recipient, uint256 amount,bool sell) private
    {
        if(!_tradingEnabled)
        {
            _feelessTransfer(sender, recipient, amount);
        }
        else
        {
            require(!sell);
            _feelessTransfer(sender, recipient, amount);
        }
    }
    
    //Applies taxes and transfers remaining tokens, 
    //All regular transfers run through this function.
    function _taxedTransfer(address sender, address recipient, 
    uint256 amount,bool isBuy,bool isSell) private
    {
        uint256 recipientBalance = _balances[recipient];
        uint256 senderBalance = _balances[sender];
        require(senderBalance >= amount, "Transfer exceeds balance");

        Tax memory tax;
        if(isSell)
        {
            //When the last Sell is less than the sellLockTime ago, sells are disabled
            require(_sellLock[sender]<=block.timestamp,"Seller in sellLock");
            
            //Sells can't exceed the sell limit(50.000 Tokens at start)
            require(amount<=_sellLimit,"Dump protection");
            
            //Sets the sell lock for the sender so the seller can't sell for a given time
            _sellLock[sender]=block.timestamp+_sellLockTime;

            tax=_sellTax;
        }
        else
        {
            //Require the final balance(excluding Taxes) to be less than the balance Limit.
            //That means you can buy a maximum of 500.000 Token at Start and recieve 400.000 Token at 20% tax
            //After that you can still buy 100.000 Token and so on 
            require(recipientBalance+amount<=_balanceLimit,"whale protection");
            if(isBuy)
            {
                tax=_buyTax;
            }
            else//Transfer
            {
                //Transfers are disabled in sell lock
                require(_sellLock[sender]<=block.timestamp,"Sender in Lock");

                tax=_transferTax;
            }
        }
        
        //Handle LP And Marketing BNB Generation once hold exceeds treshold
        bool isSwapPossible=((sender!=_pancakePairAddress)&&(!_manualConversion));
        
        if(_liquidityBalance>=_sellLimit/2&&isSwapPossible)
        {
            //Sell taxed token and convert them to LP witch are locked in the contract
            _swapAutoLiquidity();
        } 
        else if(_marketingBalance>=_sellLimit/2&&isSwapPossible)
        {
            //sell taxed token for BNB and leave them in the Contract Wallet to be distributed later
            _swapMarketingBNB();
        }

            
        

        //Track the amount that remains after Taxes
        uint256 taxedAmount=amount;
        
        //Calculates the exact token amount for each tax
        uint256 tokensToBeBurnt=_calculateFee(amount, tax.burn);
        uint256 marketingToken=_calculateFee(amount,tax.marketing);
        uint256 liquidityToken=_calculateFee(amount,tax.liquidity);
        //Subtract the Taxed Tokens 
        taxedAmount-=(tokensToBeBurnt+marketingToken+liquidityToken);

        //Adds the taxed tokens to the contract wallet
        _marketingBalance+=marketingToken;
        _liquidityBalance+=liquidityToken;
        _balances[address(this)] += marketingToken+liquidityToken;
        
        //Transfers the tokens
        _balances[sender]-=amount;
        _balances[recipient]+=taxedAmount;
        //Burns tokens
        _totalSupply-=tokensToBeBurnt;

        emit Transfer(sender,recipient,taxedAmount);
    }

    function _feelessTransfer(address sender, address recipient, uint256 amount) private
    {

        uint256 senderBalance = _balances[sender];
        require(senderBalance >= amount, "Transfer exceeds balance");
        _balances[sender]=senderBalance-amount;
        _balances[recipient]+=amount;

        emit Transfer(sender,recipient,amount);
    }

 
    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    //Functions to convert Taxes to LP and BNB//////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    function _swapAutoLiquidity() private lockTheSwap{
        _isSwappingContractToken=true;
        
        //make sure to swap less tokens than balance
        uint256 token=_liquidityBalance;
        _liquidityBalance=0;
        uint256 _tokenBalance=_balances[address(this)];
        if(token>_tokenBalance)
        {
            token=_tokenBalance;
        }
        //split token in 2 halves
        uint256 half = token / 2;
        uint256 otherHalf=token-half;
        
        //swap otherHalf for BNB
        uint256 initialBNBBalance = address(this).balance;
        _swapTokenForBNB(otherHalf);
        uint256 newBalance = address(this).balance - initialBNBBalance;
        
        //adds tokens and BNB to liquidity
        _addLiquidity(half, newBalance);
        _isSwappingContractToken=false;
    }
    
    function _swapMarketingBNB() private lockTheSwap{
        _isSwappingContractToken=true;
    
        //make sure to swap less tokens than balance
        uint256 token=_marketingBalance;
        _marketingBalance=0;
        uint256 _tokenBalance=_balances[address(this)];
        if(token>_tokenBalance)
        {
            token=_tokenBalance;
        }
        //Do The Swap
        _swapTokenForBNB(token);
        _isSwappingContractToken=false;
    }
    
    //helper function to swap tokens on contract address to BNB
    function _swapTokenForBNB(uint256 amount) private {
        _approve(address(this), address(_pancakeRouter), amount);

        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = _pancakeRouter.WETH();

        _pancakeRouter.swapExactTokensForETHSupportingFeeOnTransferTokens(
            amount,
            0,
            path,
            address(this),
            block.timestamp
        );
    }
    //helper function to swap tokens and BNB for LP-Token
    function _addLiquidity(uint256 tokenAmount, uint256 bnbAmount) private {
        _approve(address(this), address(_pancakeRouter), tokenAmount);
        
        _pancakeRouter.addLiquidityETH{value: bnbAmount}(
            address(this),
            tokenAmount,
            0,
            0,
            address(this),
            block.timestamp
        );
    }



    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    //Functions to handle MarketingBNB//////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    
    //TODO: Change Marketing Wallets, Donation Wallets, and _releaseFrequency
    //How often do the Marketing BNB get Released
    uint256 constant _releaseFrequency=2 minutes;
    
    //Time of the next release of MarketingBNB
    uint256 private _nextBNBRelease;

    bool private _manualConversion;
    
    //List of availavle donationWallets
    address[] _donationWallets=[0x0c9778964B5596E5f95c23a1b2E93833f7c01Ae5,0x51d8254866042fd1f512CAEE4a11218061AA2636];
    //Active donationWallet
    address private _donationWallet;

    //The Team Wallet is a Multisig wallet that reqires 3 signatures for each action
    address _teamWallet=0xb1719703eBE28d27eD38c81429724160B2aCeb8B;
    address private _marketingWallet;
    
    
    
    bool _useDonationInsteadOfMarketing;
    
    function aDonateMarketingWallet(bool useDonationWallet) public onlyTeam{
        _useDonationInsteadOfMarketing=useDonationWallet;
        if(useDonationWallet)
        {
            _marketingWallet=_donationWallet;
        }
        else
        {
            _marketingWallet=_teamWallet;
        }
    }
    
    function aSetDonationAddress(uint ID) public onlyTeam{
        require(ID<_donationWallets.length,"DonationAdresses doesnt exist");
        _donationWallet=_donationWallets[ID];
        if(_useDonationInsteadOfMarketing)
        {
            _marketingWallet=_donationWallet;
        }
    }
    
    function aSwitchManualContractTokenConversion(bool manualConversion) public onlyTeam{
        _manualConversion=manualConversion;
    }



    
    function _releaseBNB() public onlyTeam{
    
        if(_nextBNBRelease<=block.timestamp)
        {
            return;
        }
        uint256 amount=address(this).balance;
        uint256 donateAmount=amount/7;
        amount-=donateAmount;
        _releaseMarketingBNB(amount);
        _donateBNB(donateAmount);
      
        _nextBNBRelease=_nextBNBRelease+_releaseFrequency;
    }
    
    //Transfer to Marketing Wallet
    function _releaseMarketingBNB(uint256 amount) private {
        _marketingWallet.call{value: (amount)}("");
    }
    
    //Donate to Donation Address
    function _donateBNB(uint256 amount) private {
       _donationWallet.call{value: (amount)}("");
    }

    
    
    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    //Settings//////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    uint256 private constant _maxTax=20;
    uint256 private constant _maxMarketingTax=5;
    //Disables the owner from changing taxes
    bool _setTaxesDisabled;
    function aDisableSetTaxes() public onlyTeam
    {
        _setTaxesDisabled=true;
    }
    //Function to set the taxes, can only be called once in 23 hours
    uint256 _lastSetTaxes;
    function aSetTaxes(uint256 burnTax, uint256 liquidityTax, uint256 marketingTax,bool buy,bool sell, bool transfer) public onlyTeam
    {
        require(!_setTaxesDisabled,"Set Taxes was disabled");
        require(_lastSetTaxes+23 hours<block.timestamp,"Taxes can only be changed once a day");
        require(marketingTax<=_maxMarketingTax,"marketingTax higher than maxMarketingTax");
        uint256 totalTax=burnTax+liquidityTax+marketingTax;
        require(totalTax<=_maxTax,"total tax higher than maxTax");
        
        Tax memory newTax=Tax(burnTax,liquidityTax,marketingTax);
        if(buy)
        {
            _buyTax=newTax;
        }
        if(sell)
        {
            _sellTax=newTax;
        }
        if(transfer)
        {
             _transferTax=newTax;
        }
        _lastSetTaxes=block.timestamp;
    }


    function getBuyTax() public view returns(uint,uint,uint){
        return (_buyTax.burn,_buyTax.liquidity,_buyTax.marketing);
    }
    
    function getSellTax() public view returns(uint,uint,uint){
        return (_sellTax.burn,_sellTax.liquidity,_sellTax.marketing);
    }
    
    function getTransferTax() public view returns(uint,uint,uint){
        return (_transferTax.burn,_transferTax.liquidity,_transferTax.marketing);
    }


    
    function _calculateFee(uint256 amount, uint256 tax) private pure returns (uint256) {
        uint256 fee = (amount*tax) / 100;
        return fee;
    }
   

    //manually convert token on contract
    function aConvertContractToken() public onlyTeam
    {
        _swapAutoLiquidity();
        _swapMarketingBNB();
    }
    
    //Exclude/Include account from fees (eg. CEX), owner can't be excluded
    function aExcludeAccountFromFees(address account) public onlyTeam {
        require(account!=owner());
        _excluded.add(account);
    }
    function aIncludeAccountToFees(address account) public onlyTeam {
        _excluded.remove(account);
    }

    
    //Updates Limits to the current supply
    function aUpdateLimits() public onlyTeam{
        _sellLimit = _totalSupply * 5 / 1000;      // 50.000 Token at start
        _balanceLimit = _totalSupply * 5 / 100;    //500.000 Token at start
    }
    
    


    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    //Critical Functions////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    bool _tradingEnabled;
    bool private _LPTokenAddressDeclared=false;
    address private _liquidityTokenAddress;
    function getLiquidityTokenAddress() public view returns(address){
        return _liquidityTokenAddress;
    }

    //TODO change release to 1 day and unlock time to 7 days
    uint256 _whiteListTradingTime;
    function aUnlockTrading() public onlyOwner{
        require(_liquidityTokenAddress!=address(0),"LP Token not yet declared");
        require(_whiteListTradingTime==0,"Trading already Enabled");
        aUpdateLimits();      
        _whiteListTradingTime=block.timestamp+5 minutes;
        _nextBNBRelease=block.timestamp+10 minutes;
        _liquidityUnlockTime=block.timestamp+7 minutes;
    }

    function aAddToWhitelist(address addressToAdd) public onlyOwner{
        _whiteList.add(addressToAdd);
    }
    function aAddArrayToWhitelist(address[] memory addressesToAdd) public onlyOwner{
        for(uint i=0; i<addressesToAdd.length; i++)
        {
            _whiteList.add(addressesToAdd[i]);
        }
    }
    
    //Sets liquidityTokenAddress required for setup
    function aSetupLiquidityTokenAddress(address liquidityTokenAddress) public onlyOwner{
        require(!_tradingEnabled,"This function is locked forever");
        _liquidityTokenAddress=liquidityTokenAddress;
    }
    

    

    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    //Liquidity Lock////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////



    
    
    uint256 private _liquidityUnlockTime;

    //Sets Liquidity Release to 20% and makes a complete rugpull impossible, even if the unlock time is over 
    //Should be called once start was successful
    bool private _liquidityRelease20Percent;
    function limitLiquidityReleaseTo20Percent() public onlyTeam{
        _liquidityRelease20Percent=true;
    }
    //TestFunction
    function unlockLiquidityIn10Minutes() public onlyTeam{
        uint256 newUnlockTime=block.timestamp+10 minutes; 
        require(newUnlockTime>_liquidityUnlockTime);
        _liquidityUnlockTime=newUnlockTime;
    }
    
    function unlockLiquidityInWeek() public onlyTeam{
        uint256 newUnlockTime=block.timestamp+7 days; 
        require(newUnlockTime>_liquidityUnlockTime);
        _liquidityUnlockTime=newUnlockTime;
    }
    function unlockLiquidityIn6Months() public onlyTeam{
        uint256 newUnlockTime=block.timestamp+180 days; 
        require(newUnlockTime>_liquidityUnlockTime);
        _liquidityUnlockTime=newUnlockTime;
    }
    function unlockLiquidityInAYear() public onlyTeam{
        uint256 newUnlockTime=block.timestamp+365 days; 
        require(newUnlockTime>_liquidityUnlockTime);
        _liquidityUnlockTime=newUnlockTime;
    }
    

    //TODO: Change release to 20% prolong liquidity lock to a week
    //Release Liquidity Tokens once time is over
    function _releaseLiquidity() public onlyTeam {
        //Only Callable if liquidity Unlock time is over
        require(block.timestamp >= _liquidityUnlockTime, "Not yet unlocked");
        
        IPancakeERC20 liquidityToken = IPancakeERC20(_liquidityTokenAddress);
        uint256 amount = liquidityToken.balanceOf(address(this));
        if(_liquidityRelease20Percent)
        {
        //regular liquidity release, only releases 20% at a time so a rugpull is impossible, even if the project is dead
        //TODO: Change Amount
        amount=amount*9/10;
        liquidityToken.transfer(_teamWallet, amount);
        //Automatically prolong the lock for a week TODO change to a week
        _liquidityUnlockTime=block.timestamp+1 minutes;
        }
        else
        {
            //Liquidity release if something goes wrong at start
            //_liquidityRelease20Percent should be called once everything is clear
            liquidityToken.transfer(_teamWallet, amount);
        }
    }
    




    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////

    receive() external payable {}
    fallback() external payable {}
    // IBEP20

    function getOwner() external view override returns (address) {
        return owner();
    }

    function name() external view override returns (string memory) {
        return _name;
    }

    function symbol() external view override returns (string memory) {
        return _symbol;
    }

    function decimals() external view override returns (uint8) {
        return _decimals;
    }

    function totalSupply() external view override returns (uint256) {
        return _totalSupply;
    }

    function balanceOf(address account) external view override returns (uint256) {
        return _balances[account];
    }

    function transfer(address recipient, uint256 amount) external override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    function allowance(address _owner, address spender) external view override returns (uint256) {
        return _allowances[_owner][spender];
    }

    function approve(address spender, uint256 amount) external override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }
    function _approve(address owner, address spender, uint256 amount) private {
        require(owner != address(0), "Approve from zero");
        require(spender != address(0), "Approve to zero");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    function transferFrom(address sender, address recipient, uint256 amount) external override returns (bool) {
        _transfer(sender, recipient, amount);

        uint256 currentAllowance = _allowances[sender][_msgSender()];
        require(currentAllowance >= amount, "Transfer > allowance");

        _approve(sender, _msgSender(), currentAllowance - amount);
        return true;
    }

    // IBEP20 - Helpers

    function increaseAllowance(address spender, uint256 addedValue) external returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender] + addedValue);
        return true;
    }

    function decreaseAllowance(address spender, uint256 subtractedValue) external returns (bool) {
        uint256 currentAllowance = _allowances[_msgSender()][spender];
        require(currentAllowance >= subtractedValue, "<0 allowance");

        _approve(_msgSender(), spender, currentAllowance - subtractedValue);
        return true;
    }

}
