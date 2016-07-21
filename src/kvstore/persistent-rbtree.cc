/*
 * This is a copy of the persistent red black tree that we have adapted for
 * our purposes. we have changed this significantly, but want to a keep around
 * a copy of the original.
 *
 * http://codereview.stackexchange.com/questions/119728/persistent-set-red-black-tree-follow-up
 */
#pragma once

#include <functional>
#include <utility>
#include <iostream>
#include <stack>
#include <memory>
#include <deque>
#include <iterator>     
#include <type_traits>  
#include <stack>
#include <stdexcept>
#include <vector>

namespace dts
{

	template <typename T, typename Func = std::less<T>>
		class PersistentSet
		{

		 public:

			PersistentSet();
			PersistentSet(Func);


			bool add(const T&);
			bool add(T&&);

			bool remove(const T&);

			bool empty() const;

			size_t history_size() const;

			void roll_back();

			class TreeIterator
				: public std::iterator<std::forward_iterator_tag,
				std::remove_cv_t<T>,
				std::ptrdiff_t,
				const T*,
				const T&>
			{
				using node = typename dts::PersistentSet
					<   std::remove_cv_t<T>, 
				Func
					>::Nodeptr;
				node itr;
				node nil;
				std::stack<node> path;

				node find_successor(node n)
				{
					n = n->right;
					if (n != nil)
					{
						while (n->left != nil)
						{
							path.push(n);
							n = n->left;
						}
					}
					else
					{
						n = path.top();
						path.pop();
					}
					return n;
				}
			 public:

				explicit TreeIterator(node n, node pnil) : nil(pnil) //begin
				{
					if (n == nil)
						itr = nil;
					else
					{
						path.push(nil);
						while (n->left != nil)
						{
							path.push(n);
							n = n->left;
						}
						itr = n;
					}
				}
				explicit TreeIterator(node pnil) // end
					: itr(pnil), nil(pnil)
				{ }


				TreeIterator& operator++ ()
				{
					itr = find_successor(itr);
					return *this;
				}
				TreeIterator operator++ (int)
				{
					TreeIterator tmp(*this);
					itr = find_successor(itr);
					return tmp;
				}

				bool operator == (const TreeIterator& rhs) const
				{
					return itr == rhs.itr;
				}

				bool operator != (const TreeIterator& rhs) const
				{
					return itr != rhs.itr;
				}

				const T& operator* () const
				{
					return itr->key;
				}

				const T& operator-> () const
				{
					return itr->key;
				}

			};


			typedef TreeIterator const_iterator;

			const_iterator begin() const
			{
				return begin(roots.size() - 1);
			}
			const_iterator begin(size_t index) const
			{
				if (index >= roots.size())
					throw std::out_of_range("out of range");

				return const_iterator(roots[index], nil);
			}
			const_iterator end() const
			{
				return const_iterator(nil);
			}

		 private:

			struct Node;
			using Nodeptr = std::shared_ptr<Node>;

			struct Node
			{
				T key;
				bool isRed;

				Nodeptr left;
				Nodeptr right;

				Node(const T& pkey, bool pisRed, Nodeptr pleft, Nodeptr pright)
					: key(pkey), isRed(pisRed), left(pleft), right(pright)
				{ }

				Node(T&& pkey, bool pisRed, Nodeptr pleft, Nodeptr pright)
					: key(std::move(pkey)), isRed(pisRed), left(pleft), right(pright)
				{ }
			};

			std::vector<Nodeptr> roots;
			Func cmp;
			Nodeptr nil;

			template <typename TT>
				Nodeptr create_node(TT&&);

			Nodeptr copy_node(Nodeptr) const;

			template <typename TT>
				bool generic_add(TT&&);

			template <typename TT>
				Nodeptr add_recursive(std::deque<Nodeptr>&, TT&&, Nodeptr&);

			void balance_add(std::deque<Nodeptr> &x);

			template <typename ChildA, typename ChildB>
				void mirror_add_balance(Nodeptr&, Nodeptr&, std::deque<Nodeptr>&, ChildA, ChildB);

			Nodeptr remove_recursive(const T&, Nodeptr, std::deque<Nodeptr>&);

			template<typename F, typename NF, typename TT>
				Nodeptr find_and_build(TT&&, Nodeptr, std::deque<Nodeptr>&, F, NF);

			void delete_node(std::deque<Nodeptr> &);

			Nodeptr build_min_path(Nodeptr node, std::deque<Nodeptr>&);

			void transplant(Nodeptr, Nodeptr, Nodeptr);

			void balance_remove(Nodeptr x, std::deque<Nodeptr>&);

			template <typename ChildA, typename ChildB >
				void mirror_remove_balance(Nodeptr&, Nodeptr&, std::deque<Nodeptr> &, ChildA, ChildB);

			template <typename ChildA, typename ChildB >
				Nodeptr rotate(Nodeptr, Nodeptr, ChildA, ChildB);

			static Nodeptr& left(Nodeptr x) { return x->left; };

			static Nodeptr& right(Nodeptr x) { return x->right; };

			static Nodeptr pop_front(std::deque<Nodeptr>& deque)
			{
				auto front = deque.front();
				deque.pop_front();
				return front;

			};



		};

	template<typename T, typename Func>
		size_t  PersistentSet<T, Func>::history_size() const
		{
			return roots.size();
		}
	template<typename T, typename Func>
		bool PersistentSet<T, Func>::empty() const
		{
			return roots.back() == nil;
		}

	template<typename T, typename Func>
		void  PersistentSet<T, Func>::roll_back()
		{
			if (!roots.empty())
				roots.pop_back();
		}

	template <typename K, typename Func>
		void PersistentSet<K, Func>::transplant(

				Nodeptr parent,
				Nodeptr removed,
				Nodeptr transplanted
				)
		{
			if (parent == nil)
			{
				roots.pop_back();
				roots.push_back(transplanted);
			}
			else if (parent->left == removed)
				parent->left = transplanted;
			else
				parent->right = transplanted;
		}


	template<typename T, typename Func>
		PersistentSet<T, Func>::PersistentSet() : PersistentSet(Func())
	{ }

	template<typename T, typename Func>
		PersistentSet<T, Func>::PersistentSet(Func pcmp)
		: cmp(pcmp),
		roots(std::vector<Nodeptr>()),
		nil(std::make_shared<Node>(T(), false, nullptr, nullptr))
	{
		roots.push_back(nil);
	}

	template<typename T, typename Func>
		template <typename ChildA, typename ChildB >
		typename  PersistentSet<T, Func>::Nodeptr
		PersistentSet<T, Func>::rotate(

				Nodeptr parent_of_x,
				Nodeptr x,
				ChildA childA,
				ChildB childB
				)
		{
			Nodeptr child_of_x = childB(x);
			childB(x) = childA(child_of_x);

			if (x == roots.back())
			{
				roots.pop_back();
				roots.push_back(child_of_x);
			}
			else if (x == childA(parent_of_x))
				childA(parent_of_x) = child_of_x;
			else
				childB(parent_of_x) = child_of_x;

			childA(child_of_x) = x;

			return child_of_x;
		}

	template <typename T, typename Func>
		template<typename TT>
		bool PersistentSet<T, Func>::generic_add(TT&& element)
		{

			std::deque<Nodeptr> path;
			auto newRoot = add_recursive(
					path,
					std::forward<TT>(element),
					roots.back()
					);

			bool added = newRoot != nullptr;
			if (added)
			{
				roots.push_back(newRoot);
				path.push_back(nil);
				balance_add(path);
			}
			return added;
		}

	template<typename T, typename Func>
		template<typename F, typename NF, typename TT>
		typename PersistentSet<T, Func>::Nodeptr
		PersistentSet<T, Func>::find_and_build(
				TT&& element,
				Nodeptr node,
				std::deque<Nodeptr> &path,
				F if_found,
				NF if_not_found
				)
		{
			if (node == nil)
				return if_not_found(element, path);

			bool is_less = cmp(element, node->key);
			bool is_equal = !is_less
				&& !cmp(node->key, element);

			if (is_equal)
				return if_found(node, path);

			auto direction = is_less ? left : right;
			auto child = find_and_build(
					std::forward<TT>(element),
					direction(node),
					path,
					if_found,
					if_not_found
					);
			if (child == nullptr) return child;

			auto copy = copy_node(node);
			path.push_back(copy);
			direction(copy) = child;

			return copy;
		}

	template<typename T, typename Func>
		template<typename TT>
		typename PersistentSet<T, Func>::Nodeptr
		PersistentSet<T, Func>::add_recursive(std::deque<Nodeptr>& path, TT &&element, Nodeptr & node)
		{

			auto if_not_found = [&](auto pelement, auto& path)
			{
				auto copy = create_node(std::forward<T>(pelement));
				path.push_back(copy);
				return copy;
			};
			auto if_found = [](auto node, auto& path) { return nullptr; };
			return find_and_build(element, node, path, if_found, if_not_found);
		}

	template <typename T, typename Func>
		typename PersistentSet<T, Func>::Nodeptr
		PersistentSet<T, Func>::remove_recursive(const T& element, Nodeptr node, std::deque<Nodeptr>& path)
		{

			auto if_not_found = [](auto element, auto& path) { return nullptr; };
			auto if_found = [&](auto pnode, auto& ppath)
			{
				auto copy = copy_node(pnode);
				ppath.push_back(copy);
				return copy;
			};
			return find_and_build(element, node, path, if_found, if_not_found);
		}

	template <typename T, typename Func>
		bool PersistentSet<T, Func>::add(const T& element)
		{
			return generic_add(const_cast<T&> (element));
		}

	template <typename T, typename Func>
		bool PersistentSet<T, Func>::add(T&& element)
		{
			return generic_add(std::move(element));
		}

	template<typename T, typename Func>
		typename PersistentSet<T, Func>::Nodeptr
		PersistentSet<T, Func>::copy_node(Nodeptr node) const
		{
			if (node == nil) return nil;
			return std::make_shared<Node>(node->key, node->isRed, node->left, node->right);
		}

	template <typename T, typename Func>
		template <typename TT>
		typename PersistentSet<T, Func>::Nodeptr
		PersistentSet<T, Func>::create_node(TT&& key)
		{
			return std::make_shared<Node>(std::forward<TT>(key), true, nil, nil);
		}

	template <typename T, typename Func>
		void PersistentSet<T, Func>::delete_node(std::deque<Nodeptr> & path)
		{

			auto removed = path.front();
			auto transplanted = removed->right;

			if (removed->left == nil)
			{
				path.pop_front();
				transplant(path.front(), removed, transplanted);
			}
			else if (removed->right == nil)
			{
				path.pop_front();
				transplanted = removed->left;
				transplant(path.front(), removed, transplanted);
			}
			else
			{
				auto temp = removed;
				removed->right = copy_node(removed->right);
				removed = build_min_path(removed->right, path);
				transplanted = removed->right;
				temp->key = std::move(removed->key);
				transplant(path.front(), removed, transplanted);
			}

			if (!removed->isRed)
				balance_remove(transplanted, path);

		}


	template <typename T, typename Func>
		typename PersistentSet<T, Func>::Nodeptr
		PersistentSet<T, Func>::build_min_path(Nodeptr node, std::deque<Nodeptr>& path)
		{
			while (node->left != nil)
			{
				node->left = copy_node(node->left);
				path.push_front(node);
				node = node->left;
			}
			return node;
		}

	template <typename T, typename Func>
		void PersistentSet<T, Func>::balance_remove(Nodeptr extra_black, std::deque<Nodeptr>& path)
		{

			auto parent = pop_front(path);
			while (extra_black != roots.back()
					&& !extra_black->isRed)
			{
				if (parent->left == extra_black)
					mirror_remove_balance(extra_black, parent, path, left, right);
				else
					mirror_remove_balance(extra_black, parent, path, right, left);
			}

			auto new_node = copy_node(extra_black);
			transplant(parent, extra_black, new_node);
			new_node->isRed = false;

		}
	template <typename T, typename Func>
		template <typename ChildA, typename ChildB >
		void PersistentSet<T, Func>::mirror_remove_balance(

				Nodeptr& extra_black,
				Nodeptr& parent,
				std::deque<Nodeptr> & path,
				ChildA childA,
				ChildB childB)
		{
			Nodeptr brother = childB(parent);
			if (brother->isRed)
			{
				brother = childB(parent) = copy_node(brother);

				std::swap(brother->isRed, parent->isRed);
				rotate(path.front(), parent, childA, childB);
				path.push_front(brother);
				brother = childB(parent);
			}
			if (!brother->left->isRed && !brother->right->isRed)
			{
				brother = childB(parent) = copy_node(brother);

				brother->isRed = true;
				extra_black = parent;
				parent = pop_front(path);
			}
			else
			{
				if (!childB(brother)->isRed)
				{
					brother = childB(parent) = copy_node(brother);

					childA(brother) = copy_node(childA(brother));
					std::swap(brother->isRed, childA(brother)->isRed);
					brother = rotate(parent, brother, childB, childA);
				}
				brother = childB(parent) = copy_node(brother);

				childB(brother) = copy_node(childB(brother));
				brother->isRed = parent->isRed;
				parent->isRed = false;
				childB(brother)->isRed = false;
				rotate(path.front(), parent, childA, childB);

				extra_black = roots.back();
				parent = nil;
			}

		}

	template <typename T, typename Func>
		bool PersistentSet<T, Func>::remove(const T& element)
		{
			std::deque<Nodeptr> path;

			auto node = remove_recursive(
					element,
					roots.back(),
					path
					);
			bool exist = node != nullptr;
			if (exist)
			{
				roots.push_back(node);
				path.push_back(nil);
				delete_node(path);
			}
			return exist;
		}


	template <typename T, typename Func>
		void PersistentSet<T, Func>::balance_add(std::deque<Nodeptr>& path)
		{

			auto no_compliant = pop_front(path);
			auto parent = pop_front(path);

			while (parent->isRed)
			{
				if (path.front()->left == parent)
					mirror_add_balance(parent, no_compliant, path, left, right);
				else
					mirror_add_balance(parent, no_compliant, path, right, left);
			}
			roots.back()->isRed = false;

		}

	template <typename T, typename Func>
		template <typename ChildA, typename ChildB >
		void PersistentSet<T, Func>::
		mirror_add_balance(

				Nodeptr &parent,
				Nodeptr &no_compliant,
				std::deque<Nodeptr>& path,
				ChildA childA,
				ChildB childB
				)

		{
			Nodeptr &uncle = childB(path.front());
			if (uncle->isRed)
			{
				uncle = copy_node(uncle);
				parent->isRed = false;
				uncle->isRed = false;
				path.front()->isRed = true;
				no_compliant = pop_front(path);
				parent = pop_front(path);
			}
			else
			{
				if (no_compliant == childB(parent))
				{
					std::swap(no_compliant, parent);
					rotate(path.front(), no_compliant, childA, childB);
				}
				auto grand_parent = pop_front(path);
				std::swap(grand_parent->isRed, parent->isRed);
				rotate(path.front(), grand_parent, childB, childA);
			}
		}

}
